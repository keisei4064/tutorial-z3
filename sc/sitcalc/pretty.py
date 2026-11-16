"""Z3 の論理式を本書の記法で表示する

本書の記法 (§16.1 以降) に寄せる:

- 結合子は ``∧ ∨ ¬ ⊃ ≡``，量化子は ``∀x. φ`` / ``∃x. φ`` (p.656 の書き方)
- ``Holds(F(t1, ..., tn), s)`` は ``F(t1, ..., tn, s)`` と略記する
  (p.651: "we often write clear(x, s) ...
  which as we mentioned earlier, is just a shorthand for Holds(clear(x), s)")
- ``¬(x = y)`` は ``x ≠ y``

Z3 の量化子は内部で de Bruijn 添字 (``Var(i)``) を使うので，束縛変数の名前を
スタックで管理して元の名前に戻す
"""

import z3

_BINARY = {"and": " ∧ ", "or": " ∨ ", "=>": " ⊃ "}


def show(e: z3.ExprRef, *, shorthand: bool = True) -> str:
    """論理式・項を本書の記法の文字列にする

    Args:
        e: Z3 の式
        shorthand: ``Holds(F(t1, ..., tn), s)`` を ``F(t1, ..., tn, s)`` と略記するか

    Returns:
        本書の記法の文字列 (例: ``clear(u, do(a, s)) ≡ a = putdown(u) ∨ …``)
    """
    return _render(e, [], shorthand=shorthand)


def _is_compound(e: z3.ExprRef) -> bool:
    """結合子・量化子を頂点に持つ式か (括弧が要るか) を判定する

    Args:
        e: Z3 の式

    Returns:
        部分式として表示するときに括弧が要るなら True
    """
    if z3.is_quantifier(e):
        return True
    if not z3.is_app(e):
        return False
    name = e.decl().name()
    if name in _BINARY or name == "if":
        return e.num_args() > 1
    if name == "=":
        # 項の等式 (a = stack(x, y)) は結合子より強く結合するので括弧不要．論理式の ≡ は要る
        return z3.is_bool(e.arg(0))
    return False


def _is_equality(e: z3.ExprRef) -> bool:
    """2 項の等式 ``t1 = t2`` かを判定する

    Args:
        e: Z3 の式

    Returns:
        等式なら True
    """
    return z3.is_app(e) and e.decl().name() == "=" and e.num_args() == 2  # noqa: PLR2004


def _flatten(name: str, args: list[z3.ExprRef]) -> list[z3.ExprRef]:
    """同じ結合子の入れ子を平らにする

    例: (φ ∨ ψ) ∨ χ を φ ∨ ψ ∨ χ に

    Args:
        name: 結合子の名前 (``"and"`` / ``"or"``)
        args: 結合子の引数

    Returns:
        平らにした引数のリスト
    """
    flat: list[z3.ExprRef] = []
    for arg in args:
        if z3.is_app(arg) and arg.decl().name() == name and arg.num_args() > 1:
            flat.extend(_flatten(name, arg.children()))
        else:
            flat.append(arg)
    return flat


def _wrap(e: z3.ExprRef, bound: list[str], *, shorthand: bool) -> str:
    """部分式を表示し，必要なら括弧で囲む

    Args:
        e: Z3 の式
        bound: 外側の量化子で束縛された変数名 (内側ほど後ろ)
        shorthand: Holds の略記をするか

    Returns:
        表示用の文字列
    """
    s = _render(e, bound, shorthand=shorthand)
    return f"({s})" if _is_compound(e) else s


def _render(e: z3.ExprRef, bound: list[str], *, shorthand: bool) -> str:  # noqa: C901, PLR0911, PLR0912
    """式を本書の記法で表示する (再帰)

    量化子の本体の de Bruijn 添字 ``Var(i)`` は，bound の後ろから i 番目の名前に戻す

    Args:
        e: Z3 の式
        bound: 外側の量化子で束縛された変数名 (内側ほど後ろ)
        shorthand: Holds の略記をするか

    Returns:
        表示用の文字列
    """
    if z3.is_var(e):
        return bound[-1 - z3.get_var_index(e)]
    if isinstance(e, z3.QuantifierRef):
        names = [e.var_name(i) for i in range(e.num_vars())]
        symbol = "∀" if e.is_forall() else "∃"
        body = _render(e.body(), [*bound, *names], shorthand=shorthand)
        return f"{symbol}{', '.join(names)}. {body}"
    if not z3.is_app(e):
        return str(e)

    name = e.decl().name()
    args = e.children()
    if name in _BINARY and len(args) > 1:
        if name in {"and", "or"}:
            args = _flatten(name, args)
        return _BINARY[name].join(_wrap(a, bound, shorthand=shorthand) for a in args)
    if name in _BINARY and len(args) == 1:
        return _render(args[0], bound, shorthand=shorthand)
    if name == "and" and not args:
        return "true"
    if name == "or" and not args:
        return "false"
    if name == "not":
        inner = args[0]
        if _is_equality(inner) and not z3.is_bool(inner.arg(0)):
            lhs, rhs = inner.children()
            left = _render(lhs, bound, shorthand=shorthand)
            right = _render(rhs, bound, shorthand=shorthand)
            return f"{left} ≠ {right}"
        return "¬" + _wrap(inner, bound, shorthand=shorthand)
    if name == "=" and len(args) == 2:  # noqa: PLR2004
        op = " ≡ " if z3.is_bool(args[0]) else " = "
        return op.join(_wrap(a, bound, shorthand=shorthand) for a in args)
    if name == "distinct" and len(args) == 2:  # noqa: PLR2004
        return " ≠ ".join(_wrap(a, bound, shorthand=shorthand) for a in args)
    if name == "if" and len(args) == 3:  # noqa: PLR2004
        c, t, f = (_render(a, bound, shorthand=shorthand) for a in args)
        return f"if {c} then {t} else {f}"
    if shorthand and name == "Holds" and len(args) == 2 and z3.is_app(args[0]):  # noqa: PLR2004
        fluent, situation = args
        inner = [_render(a, bound, shorthand=shorthand) for a in fluent.children()]
        inner.append(_render(situation, bound, shorthand=shorthand))
        return f"{fluent.decl().name()}({', '.join(inner)})"
    if not args:
        return name
    return f"{name}({', '.join(_render(a, bound, shorthand=shorthand) for a in args)})"
