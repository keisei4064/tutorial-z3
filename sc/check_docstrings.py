"""docstring の検査 (Google 形式)

ruff の pydocstyle (D) は公開 API の docstring の有無しか見ず，非公開の関数や
ネストした関数は対象外で，Args などの節の有無も強制しない．そこで ast で次を検査する:

- すべての関数・クラス (非公開・ネスト・dunder を含む) に docstring がある
- 引数 (self / cls を除く) がある関数には ``Args:`` 節があり，すべての引数が載っている
- 値を返す関数には ``Returns:`` 節がある (プロパティは属性として書くので除く)
- ジェネレータには ``Yields:`` 節がある
- 本体で例外を投げる関数には ``Raises:`` 節があり，その例外名が載っている
- 公開属性を持つクラスには ``Attributes:`` 節があり，すべての公開属性が載っている
  (クラス本体の注釈付きフィールド・代入 (Enum のメンバーなど) と，``__init__`` での
  ``self.x = ...``．``_`` で始まる名前と ``__slots__`` は除く)

句読点の規則 (docstring とコメント．``# noqa:`` などの指示コメントは除く):

- 読点・句点には全角の「，」「．」を使う (和文の読点・句点は使わない)
- 行末に句読点 (「．」「，」「.」) を付けない (省略記号 ``...`` は除く)

スタブ (``.pyi``) は句読点の規則だけを検査する

使い方 (リポジトリのルートで)::

    uv run python -m sc.check_docstrings

問題があれば一覧を表示して終了コード 1 で終わる
"""

import ast
import io
import sys
import tokenize
from collections.abc import Iterator
from pathlib import Path

ROOT = Path(__file__).resolve().parent

type FunctionNode = ast.FunctionDef | ast.AsyncFunctionDef


def _own_nodes(func: FunctionNode) -> Iterator[ast.AST]:
    """関数本体の節点のうち，ネストした関数・クラスの中身を除いたもの

    Args:
        func: 関数の節点

    Yields:
        本体の節点 (ネストした関数・クラスの節点そのものは含むが，その中身は含まない)

    """
    stack: list[ast.AST] = list(func.body)
    while stack:
        node = stack.pop()
        yield node
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef, ast.Lambda)):
            continue
        stack.extend(ast.iter_child_nodes(node))


def _parameters(func: FunctionNode) -> list[str]:
    """docstring に書くべき引数名 (self / cls を除く)

    Args:
        func: 関数の節点

    Returns:
        引数名のリスト．可変長引数は ``*args`` / ``**kwargs`` の形

    """
    args = func.args
    names = [a.arg for a in (*args.posonlyargs, *args.args, *args.kwonlyargs)]
    if args.vararg is not None:
        names.append(f"*{args.vararg.arg}")
    if args.kwarg is not None:
        names.append(f"**{args.kwarg.arg}")
    return [n for n in names if n not in {"self", "cls"}]


def _returns_value(func: FunctionNode) -> bool:
    """戻り値の注釈が None 以外か (ジェネレータは Yields で扱うので除く)

    Args:
        func: 関数の節点

    Returns:
        ``Returns:`` 節が必要なら True

    """
    ann = func.returns
    if ann is None or (isinstance(ann, ast.Constant) and ann.value is None):
        return False
    if isinstance(ann, ast.Name) and ann.id in {"None", "NoReturn", "Never"}:
        return False
    return not _is_generator(func)


def _is_generator(func: FunctionNode) -> bool:
    """本体に yield を含むか

    Args:
        func: 関数の節点

    Returns:
        ジェネレータなら True

    """
    return any(isinstance(n, (ast.Yield, ast.YieldFrom)) for n in _own_nodes(func))


def _raised(func: FunctionNode) -> set[str]:
    """本体で投げる例外のクラス名 (再送出 ``raise`` 単体は除く)

    Args:
        func: 関数の節点

    Returns:
        例外のクラス名の集合

    """
    names: set[str] = set()
    for node in _own_nodes(func):
        if not isinstance(node, ast.Raise) or node.exc is None:
            continue
        exc = node.exc.func if isinstance(node.exc, ast.Call) else node.exc
        if isinstance(exc, ast.Name):
            names.add(exc.id)
        elif isinstance(exc, ast.Attribute):
            names.add(exc.attr)
    return names


def _is_property(func: FunctionNode) -> bool:
    """プロパティ (``@property``) か

    Args:
        func: 関数の節点

    Returns:
        プロパティなら True

    """
    return any(isinstance(d, ast.Name) and d.id == "property" for d in func.decorator_list)


def _section(doc: str, name: str) -> str | None:
    """docstring の節 (``Args:`` など) の本文

    Args:
        doc: docstring
        name: 節の名前 (``"Args"`` など)

    Returns:
        節の本文 (見出しの次の行から，次の見出しまで)．節がなければ None

    """
    lines = doc.splitlines()
    for i, line in enumerate(lines):
        if line.strip() == f"{name}:":
            body: list[str] = []
            for rest in lines[i + 1 :]:
                stripped = rest.strip()
                if (
                    stripped.endswith(":")
                    and stripped[:-1].isidentifier()
                    and rest == rest.lstrip()
                ):
                    break
                body.append(rest)
            return "\n".join(body)
    return None


def _documents(section: str, name: str) -> bool:
    """節の中に ``name:`` または ``name (型):`` の行があるか

    Args:
        section: 節の本文
        name: 引数名や例外名

    Returns:
        載っていれば True

    """
    for line in section.splitlines():
        head = line.strip()
        if head.startswith((f"{name}:", f"{name} (")):
            return True
    return False


def check_function(func: FunctionNode, where: str) -> list[str]:
    """関数の docstring を検査する

    Args:
        func: 関数の節点
        where: 表示用の位置 (``ファイル:行 名前``)

    Returns:
        問題の一覧 (なければ空)

    """
    doc = ast.get_docstring(func)
    if doc is None:
        return [f"{where}: docstring がない"]
    problems: list[str] = []
    params = _parameters(func)
    if params:
        args = _section(doc, "Args")
        if args is None:
            problems.append(f"{where}: Args 節がない ({', '.join(params)})")
        else:
            missing = [
                p for p in params if not _documents(args, p) and not _documents(args, p.lstrip("*"))
            ]
            if missing:
                problems.append(f"{where}: Args に載っていない引数: {', '.join(missing)}")
    if _returns_value(func) and not _is_property(func) and _section(doc, "Returns") is None:
        problems.append(f"{where}: Returns 節がない")
    if _is_generator(func) and _section(doc, "Yields") is None:
        problems.append(f"{where}: Yields 節がない")
    raised = _raised(func)
    if raised:
        raises = _section(doc, "Raises")
        if raises is None:
            problems.append(f"{where}: Raises 節がない ({', '.join(sorted(raised))})")
        else:
            missing = [e for e in sorted(raised) if not _documents(raises, e)]
            if missing:
                problems.append(f"{where}: Raises に載っていない例外: {', '.join(missing)}")
    return problems


def _self_targets(init: ast.FunctionDef) -> list[str]:
    """``__init__`` の中で ``self.x = ...`` / ``self.x: T = ...`` と代入する属性の名前

    Args:
        init: ``__init__`` の節点

    Returns:
        属性名のリスト (出現順，重複あり)

    """
    names: list[str] = []
    for node in ast.walk(init):
        targets: list[ast.expr] = []
        if isinstance(node, ast.Assign):
            targets = list(node.targets)
        elif isinstance(node, ast.AnnAssign):
            targets = [node.target]
        names.extend(
            t.attr
            for t in targets
            if isinstance(t, ast.Attribute)
            and isinstance(t.value, ast.Name)
            and t.value.id == "self"
        )
    return names


def _public_attributes(cls: ast.ClassDef) -> list[str]:
    """クラスの公開属性の名前

    Args:
        cls: クラスの節点

    Returns:
        クラス本体の注釈付きフィールド・代入の対象と，``__init__`` で ``self`` に代入する属性の名前
        (``_`` で始まるものを除き，出現順，重複なし)

    """
    names: list[str] = []
    for stmt in cls.body:
        if isinstance(stmt, ast.AnnAssign) and isinstance(stmt.target, ast.Name):
            names.append(stmt.target.id)
        elif isinstance(stmt, ast.Assign):
            names.extend(t.id for t in stmt.targets if isinstance(t, ast.Name))
        elif isinstance(stmt, ast.FunctionDef) and stmt.name == "__init__":
            names.extend(_self_targets(stmt))
    return list(dict.fromkeys(n for n in names if not n.startswith("_")))


def check_class(cls: ast.ClassDef, where: str) -> list[str]:
    """クラスの docstring を検査する

    Args:
        cls: クラスの節点
        where: 表示用の位置 (``ファイル:行 名前``)

    Returns:
        問題の一覧 (なければ空)

    """
    doc = ast.get_docstring(cls)
    if doc is None:
        return [f"{where}: docstring がない"]
    attrs = _public_attributes(cls)
    if not attrs:
        return []
    section = _section(doc, "Attributes")
    if section is None:
        return [f"{where}: Attributes 節がない ({', '.join(attrs)})"]
    missing = [a for a in attrs if not _documents(section, a)]
    return [f"{where}: Attributes に載っていない属性: {', '.join(missing)}"] if missing else []


_DIRECTIVES = ("noqa", "type:", "pyright:", "fmt:")


def punctuation_problems(text: str, where: str) -> list[str]:
    """docstring やコメントの句読点の規則違反を探す

    Args:
        text: docstring の中身，またはコメント (先頭の ``#`` を含む)
        where: 表示用の位置

    Returns:
        問題の一覧 (なければ空)

    """
    problems: list[str] = []
    for i, line in enumerate(text.splitlines()):
        stripped = line.rstrip()
        if "、" in stripped or "。" in stripped:
            problems.append(
                f"{where} (+{i}): 「、」「。」ではなく「，」「．」を使う: {stripped.strip()}"
            )
        if stripped.endswith(("．", "，", ".")) and not stripped.endswith("..."):
            problems.append(f"{where} (+{i}): 行末の句読点は付けない: {stripped.strip()}")
    return problems


def _comment_problems(source: str, rel: Path) -> list[str]:
    """ソース中のコメントの句読点を検査する

    Args:
        source: ソースコード
        rel: 表示用のファイルパス

    Returns:
        問題の一覧 (なければ空)

    """
    problems: list[str] = []
    for tok in tokenize.generate_tokens(io.StringIO(source).readline):
        if tok.type != tokenize.COMMENT or tok.string[1:].lstrip().startswith(_DIRECTIVES):
            continue
        problems.extend(punctuation_problems(tok.string, f"{rel}:{tok.start[0]} コメント"))
    return problems


def check_file(path: Path) -> list[str]:
    """ファイル内のすべての関数・クラスを検査する

    Args:
        path: Python ファイル

    Returns:
        問題の一覧 (なければ空)

    """
    source = path.read_text(encoding="utf-8")
    tree = ast.parse(source)
    rel = path.relative_to(ROOT.parent)
    problems: list[str] = _comment_problems(source, rel)
    module_doc = ast.get_docstring(tree)
    if path.suffix == ".pyi":
        # スタブは z3 の実装の形をなぞるだけなので，句読点の規則だけを検査する
        docs = [module_doc] + [
            ast.get_docstring(n)
            for n in ast.walk(tree)
            if isinstance(n, (ast.ClassDef, ast.FunctionDef, ast.AsyncFunctionDef))
        ]
        problems.extend(p for d in docs if d is not None for p in punctuation_problems(d, f"{rel}"))
        return problems
    if module_doc is None:
        problems.append(f"{rel}: モジュールの docstring がない")
    else:
        problems.extend(punctuation_problems(module_doc, f"{rel} モジュール"))
    for node in ast.walk(tree):
        where = f"{rel}:{getattr(node, 'lineno', 0)} {getattr(node, 'name', '')}"
        if isinstance(node, ast.ClassDef):
            problems.extend(check_class(node, where))
        elif isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            problems.extend(check_function(node, where))
        else:
            continue
        doc = ast.get_docstring(node)
        if doc is not None:
            problems.extend(punctuation_problems(doc, where))
    return problems


def main() -> int:
    """sc/ 以下の .py をすべて検査する

    Returns:
        終了コード (問題がなければ 0，あれば 1)

    """
    paths = sorted(
        p
        for p in ROOT.rglob("*.py*")
        if p.suffix in {".py", ".pyi"} and "out" not in p.parts and "__pycache__" not in p.parts
    )
    problems = [msg for path in paths for msg in check_file(path)]
    for msg in problems:
        print(msg)  # noqa: T201  (CLI の出力)
    print(f"{len(paths)} ファイルを検査: 問題 {len(problems)} 件")  # noqa: T201
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
