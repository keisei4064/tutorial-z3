"""量化子の書き換え (Z3 が扱いやすい同値な形にする)

1. :func:`eliminate_constructor_quantifiers` — 構成子についての存在量化の消去
2. :func:`expand_finite_quantifiers` — 有限ソート (列挙型) 上の量化子の展開

どちらもデータ型の意味論 (一意名と領域閉包) のもとで同値な書き換えである

構成子についての存在量化の消去 (コンパイル時の最適化):

後継状態公理には ``∃x, y. a = move(x, y) ∧ φ(x, y)`` のような式が現れる
行動のデータ型では (一意名公理と領域閉包により)

    ∃x⃗. a = A(x⃗) ∧ φ(x⃗)   ≡   is_A(a) ∧ φ(A₁(a), ..., Aₙ(a))

が成り立つ (A_i はアクセサ: a = A(x⃗) なら A_i(a) = x_i)．再帰関数の本体に量化子が
残ると Z3 の探索が極端に遅くなる (再帰の展開が量化子の中で止まる) ので
:class:`sc.sitcalc.theory.CompiledTheory` を作るときにこの書き換えを行う
公理版 (BasicActionTheory.entails) では本書の形のまま使う
"""

from itertools import count

import z3

from sc.sitcalc.axioms import subterms
from sc.sitcalc.language import Formula, as_formula


def eliminate_constructor_quantifiers(phi: Formula) -> Formula:
    """``∃x⃗. t = C(x⃗) ∧ ψ`` を ``is_C(t) ∧ ψ[x⃗ := C⃗(t)]`` に書き換える

    Args:
        phi: 論理式

    Returns:
        同値な論理式
    """
    return as_formula(_eliminate(phi))


def _eliminate(e: z3.ExprRef) -> z3.ExprRef:
    """式を再帰的にたどり，消去できる存在量化子を消去する

    Args:
        e: Z3 の式

    Returns:
        書き換えた式 (消去できない量化子はそのまま)
    """
    if isinstance(e, z3.QuantifierRef):
        if e.is_exists():
            replaced = _try_eliminate(e)
            if replaced is not None:
                return _eliminate(replaced)
        return e
    if z3.is_app(e) and e.num_args() > 0:
        return e.decl()(*(_eliminate(c) for c in e.children()))
    return e


def _has_vars(e: z3.ExprRef) -> bool:
    """式が束縛変数 (de Bruijn 添字 ``Var(i)``) を含むかを判定する

    Args:
        e: Z3 の式

    Returns:
        含むなら True
    """
    return any(z3.is_var(t) for t in subterms(e))


def _try_eliminate(q: z3.QuantifierRef) -> z3.BoolRef | None:
    """``∃x⃗. ... ∧ t = C(x⃗) ∧ ...`` の形なら存在量化子を消去する

    Args:
        q: 量化子の式

    Returns:
        書き換えた式．その形でなければ None
    """
    n = q.num_vars()
    body = q.body()
    conjuncts = body.children() if z3.is_and(body) else [body]
    for k, c in enumerate(conjuncts):
        if not z3.is_eq(c):
            continue
        for pattern, term in ((c.arg(0), c.arg(1)), (c.arg(1), c.arg(0))):
            result = _match(pattern, term, n)
            if result is None:
                continue
            recognizer, replacements = result
            rest = [x for i, x in enumerate(conjuncts) if i != k]
            new_body = (
                z3.substitute_vars(z3.And(*(as_formula(x) for x in rest)), *replacements)
                if rest
                else None
            )
            parts = [as_formula(recognizer)]
            if new_body is not None:
                parts.append(as_formula(new_body))
            return z3.And(*parts) if len(parts) > 1 else parts[0]
    return None


def _match(
    pattern: z3.ExprRef, term: z3.ExprRef, n: int
) -> tuple[z3.ExprRef, list[z3.ExprRef]] | None:
    """pattern = C(Var...) の形で，term が束縛変数を含まないかを調べる

    束縛変数 0..n-1 がすべて，pattern の引数にちょうど 1 回ずつ現れることを要求する

    Args:
        pattern: 構成子の適用 (になっているはずの式)
        term: 等式の反対側の式
        n: 量化子が束縛する変数の個数

    Returns:
        (認識子 is_C(term), 各束縛変数の代わりのアクセサの適用) の組．合わなければ None
    """
    sort = pattern.sort()
    if not isinstance(sort, z3.DatatypeSortRef) or not z3.is_app(pattern) or _has_vars(term):
        return None
    for ci in range(sort.num_constructors()):
        if not pattern.decl().eq(sort.constructor(ci)):
            continue
        args = pattern.children()
        position: dict[int, int] = {}
        for j, arg in enumerate(args):
            if not z3.is_var(arg):
                return None  # 定数が混ざる引数は (簡単のため) 扱わない
            idx = z3.get_var_index(arg)
            if idx in position:
                return None
            position[idx] = j
        if set(position) != set(range(n)):
            return None
        replacements = [sort.accessor(ci, position[i])(term) for i in range(n)]
        return sort.recognizer(ci)(term), replacements
    return None


def _is_enumeration(sort: object) -> bool:
    """列挙型 (すべての構成子が 0 引数の有限データ型) かを判定する

    Args:
        sort: Z3 のソート

    Returns:
        列挙型なら True
    """
    if not isinstance(sort, z3.DatatypeSortRef):
        return False
    return all(sort.constructor(i).arity() == 0 for i in range(sort.num_constructors()))


def expand_finite_quantifiers(phi: Formula) -> Formula:
    """列挙型の変数を束縛する量化子を，全ケースの連言 (∀) / 選言 (∃) に展開する

    例: ブロックのソートが {A, B, C} なら ``∃y. on(x, y, s)`` は
    ``on(x, A, s) ∨ on(x, B, s) ∨ on(x, C, s)`` になる．列挙型の領域閉包により同値
    状況・行動・フルエントなど無限 (または引数付き構成子を持つ) のソートの量化子は残す

    Args:
        phi: 論理式

    Returns:
        同値な論理式
    """
    return as_formula(_expand(phi))


_fresh = count()


def _expand(e: z3.ExprRef) -> z3.ExprRef:
    """式を再帰的にたどり，列挙型の束縛変数を展開する

    束縛変数は一意な名前の定数に置き換えてから本体を処理し，残った (無限ソートの)
    変数で量化子を作り直す．名前が一意なので変数の捕獲は起きない

    Args:
        e: Z3 の式

    Returns:
        書き換えた式
    """
    if isinstance(e, z3.QuantifierRef):
        n = e.num_vars()
        # 束縛変数を一意な名前の定数で置き換えて本体を取り出す (変数の捕獲を避ける)
        # de Bruijn 添字: Var(k) は n-1-k 番目に束縛した変数
        tag = next(_fresh)
        fresh = [z3.Const(f"{e.var_name(i)}%{tag}", e.var_sort(i)) for i in range(n)]
        body = _expand(z3.substitute_vars(e.body(), *(fresh[n - 1 - k] for k in range(n))))
        finite = [v for v in fresh if _is_enumeration(v.sort())]
        others = [v for v in fresh if not _is_enumeration(v.sort())]
        if finite:
            instances = [
                as_formula(z3.substitute(body, *zip(finite, combo, strict=True)))
                for combo in _product([_constants(v.sort()) for v in finite])
            ]
            join = z3.And if e.is_forall() else z3.Or
            body = join(*instances) if len(instances) > 1 else instances[0]
        if not others:
            return body
        quantifier = z3.ForAll if e.is_forall() else z3.Exists
        return quantifier(others, as_formula(body))
    if z3.is_app(e) and e.num_args() > 0:
        return e.decl()(*(_expand(c) for c in e.children()))
    return e


def _constants(sort: object) -> list[z3.ExprRef]:
    """列挙型のすべての値を返す

    Args:
        sort: Z3 のソート

    Returns:
        値 (0 引数の構成子の適用) のリスト

    Raises:
        TypeError: sort がデータ型でないとき
    """
    if not isinstance(sort, z3.DatatypeSortRef):
        msg = "列挙型ではない"
        raise TypeError(msg)
    return [sort.constructor(i)() for i in range(sort.num_constructors())]


def _product(domains: list[list[z3.ExprRef]]) -> list[list[z3.ExprRef]]:
    """値の候補の直積を作る

    Args:
        domains: 変数ごとの値の候補

    Returns:
        値の組のリスト
    """
    result: list[list[z3.ExprRef]] = [[]]
    for dom in domains:
        result = [[*prefix, c] for prefix in result for c in dom]
    return result
