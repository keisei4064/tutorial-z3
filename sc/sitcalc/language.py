"""多ソート一階言語としての状況計算 (§16.1, p.651)

本書の定義:

    the situation calculus is a first-order language with the following special sorts:
    *situation*, *action*, and *fluent* (for relational fluents). There could be other
    sorts, some of them domain dependent like *block* for blocks in the blocks world ...

    - Holds(p, s) — fluent p is true in situation s;
    - do(a, s)    — the situation that results from performing action a in situation s;
    - Poss(a, s)  — action a is executable in situation s

この実装での対応:

==================  =====================================================
本書                 この実装
==================  =====================================================
sort situation       Z3 データ型 ``Situation = S0 | do(Action, Situation)``
sort action          Z3 データ型 (行動関数記号ごとに 1 構成子)
sort fluent          Z3 データ型 (関係フルエントを一階の対象として具象化 p.651)
domain sort          Z3 列挙型 (block, lock など)
Holds(p, s)          未解釈関数 ``Holds : Fluent × Situation → Bool``
do(a, s)             構成子 ``do``
Poss(a, s)           未解釈関数 ``Poss : Action × Situation → Bool``
S0                   構成子 ``S0`` (§16.3 p.661 の初期状況)
s ⊏ s'               未解釈関数 ``Precedes`` (公理は (16.64), (16.65))
Executable(s, s')    未解釈関数 ``Executable`` (定義は p.662)
==================  =====================================================

本書 p.651 にならい，関係フルエントは McCarthy の後期の流儀で一階の対象として扱い
``clear(x, s)`` は ``Holds(clear(x), s)`` の略記とする．この実装では略記を使わず
常に ``holds(clear(x), s)`` と書く．関数フルエント (functional fluent) は本書でも
例示のみなので，この実装では扱わない

Python の型との対応: 本書の各ソートの項を，それぞれ別の Python クラス
(:class:`Situation`, :class:`Action`, :class:`Fluent`, :class:`DomainObject` の
サブクラス) で包む．これにより「ソートの取り違え」(例: ``do(s, a)``) が pyright の
型エラーになる
"""

from collections.abc import Sequence
from dataclasses import dataclass
from itertools import product
from typing import override

import z3

type Formula = z3.BoolRef
"""論理式 (situation calculus formula)。Z3 の Bool 式."""


def as_formula(e: z3.ExprRef) -> Formula:
    """Z3 の式を論理式 (Bool の式) として取り出す

    Args:
        e: Z3 の式

    Returns:
        同じ式を :data:`Formula` (``BoolRef``) として

    Raises:
        TypeError: e が Bool の式でないとき
    """
    if not isinstance(e, z3.BoolRef):
        msg = f"論理式 (Bool) を期待したが {e.sort().name()} だった: {e}"
        raise TypeError(msg)
    return e


def as_datatype_term(e: z3.ExprRef) -> z3.DatatypeRef:
    """Z3 の式をデータ型の項として取り出す

    Args:
        e: Z3 の式

    Returns:
        同じ式を ``DatatypeRef`` として

    Raises:
        TypeError: e がデータ型の項でないとき
    """
    if not isinstance(e, z3.DatatypeRef):
        msg = f"データ型の項を期待したが {e.sort().name()} だった: {e}"
        raise TypeError(msg)
    return e


# ---------------------------------------------------------------------------
# 各ソートの項 (term)
# ---------------------------------------------------------------------------


class Term:
    """あるソートの項．Z3 のデータ型の式を包む

    Python の ``==`` は Z3 では「等式という論理式」を作る演算子なので
    このクラスの ``==`` は構文的な同一性 (``ExprRef.eq``) で判定する
    論理式としての等式は :func:`eq` を使う

    Attributes:
        expr: 包んでいる Z3 のデータ型の項
    """

    __slots__ = ("expr",)

    def __init__(self, expr: z3.DatatypeRef) -> None:
        """Z3 の項を包む

        Args:
            expr: 包む Z3 のデータ型の項
        """
        self.expr: z3.DatatypeRef = expr

    @override
    def __eq__(self, other: object) -> bool:
        """構文的に同じ項か (同じクラスで，Z3 の式として同一)

        Args:
            other: 比べる相手

        Returns:
            同じなら True．論理式としての等式は :func:`eq` を使う
        """
        return type(self) is type(other) and isinstance(other, Term) and self.expr.eq(other.expr)

    @override
    def __hash__(self) -> int:
        """Z3 の式のハッシュ値 (``__eq__`` と整合する)

        Returns:
            ハッシュ値
        """
        return self.expr.hash()

    @override
    def __repr__(self) -> str:
        """デバッグ用の表示 (例: ``Action(stack(A, B))``)

        Returns:
            クラス名と Z3 の式
        """
        return f"{type(self).__name__}({self.expr})"

    @override
    def __str__(self) -> str:
        """Z3 の式としての表示 (例: ``stack(A, B)``)

        Returns:
            Z3 の式の文字列
        """
        return str(self.expr)


class Situation(Term):
    """ソート situation の項 (例: ``S0``, ``do(stack(A, B), S0)``)"""

    __slots__ = ()


class Action(Term):
    """ソート action の項 (例: ``stack(A, B)``)"""

    __slots__ = ()


class Fluent(Term):
    """ソート fluent (関係フルエント) の項 (例: ``clear(A)``)"""

    __slots__ = ()


class DomainObject(Term):
    """ドメイン依存のソート (block, lock など) の項の基底クラス"""

    __slots__ = ()


def eq[T: Term](x: T, y: T) -> Formula:
    """等式 ``x = y`` を作る

    Args:
        x: 左辺の項
        y: 右辺の項 (x と同じソート)

    Returns:
        論理式 ``x = y``
    """
    return x.expr == y.expr


def ne[T: Term](x: T, y: T) -> Formula:
    """不等式 ``x ≠ y`` を作る

    Args:
        x: 左辺の項
        y: 右辺の項 (x と同じソート)

    Returns:
        論理式 ``x ≠ y``
    """
    return x.expr != y.expr


def is_variable(t: Term) -> bool:
    """項が (自由) 変数かを判定する

    0 引数の構成子 (例: ブロック A や行動 wait) も Z3 では定数なので
    構成子でない定数だけを変数とみなす

    Args:
        t: 調べる項

    Returns:
        変数なら True
    """
    e = t.expr
    if not z3.is_const(e):
        return False
    sort = e.sort()
    return not any(e.decl().eq(sort.constructor(i)) for i in range(sort.num_constructors()))


# ---------------------------------------------------------------------------
# ドメイン依存のソート
# ---------------------------------------------------------------------------


class ObjectSort[T: DomainObject]:
    """ドメイン依存のソート (有限個の名前付き対象からなる列挙型)

    列挙型なので，対象の名前の一意性 (unique names) と領域閉包
    (domain closure: 対象はこれで全部) が Z3 の意味論で自動的に成り立つ

    型パラメータ T は共変 (``ObjectSort[Block]`` は ``ObjectSort[DomainObject]`` として
    使える)．PEP 695 の変性推論で共変になるよう，属性は private にして
    読み取り専用のプロパティで公開している
    """

    __slots__ = ("_sort", "_wrap")

    def __init__(self, sort: z3.DatatypeSortRef, wrap: type[T]) -> None:
        """Z3 の列挙型と，項を包むクラスから作る

        Args:
            sort: Z3 の列挙型 (:func:`enumeration` で作る)
            wrap: このソートの項を包む Python のクラス
        """
        self._sort = sort
        self._wrap = wrap

    @property
    def sort(self) -> z3.DatatypeSortRef:
        """Z3 のソート"""
        return self._sort

    @property
    def wrap(self) -> type[T]:
        """このソートの項を包む Python のクラス"""
        return self._wrap

    @property
    def name(self) -> str:
        """ソート名"""
        return self.sort.name()

    def constants(self) -> tuple[T, ...]:
        """このソートのすべての対象を返す

        Returns:
            対象のタプル (宣言順)
        """
        return tuple(
            self.wrap(as_datatype_term(self.sort.constructor(i)()))
            for i in range(self.sort.num_constructors())
        )

    def named(self, name: str) -> T:
        """名前から対象を取り出す

        Args:
            name: 対象の名前 (例: ``"A"``)

        Returns:
            その名前の対象

        Raises:
            KeyError: その名前の対象がないとき
        """
        for c in self.constants():
            if str(c) == name:
                return c
        msg = f"ソート {self.name} に対象 {name} はない"
        raise KeyError(msg)

    def var(self, name: str) -> T:
        """このソートの変数を作る

        Args:
            name: 変数名

        Returns:
            変数 (同じ名前なら同じ Z3 定数になる)
        """
        return self.wrap(as_datatype_term(z3.Const(name, self.sort)))

    def vars(self, *names: str) -> tuple[T, ...]:
        """このソートの変数を複数作る

        Args:
            *names: 変数名

        Returns:
            変数のタプル (names と同じ順)
        """
        return tuple(self.var(n) for n in names)

    def lift(self, e: z3.ExprRef) -> T:
        """このソートの Z3 の式を，このソートの項として包む

        Args:
            e: Z3 の式

        Returns:
            包んだ項

        Raises:
            TypeError: e がデータ型の項でないか，ソートが違うとき
        """
        t = as_datatype_term(e)
        if not t.sort().eq(self.sort):
            msg = f"ソート {self.name} の項を期待したが {t.sort().name()} だった: {t}"
            raise TypeError(msg)
        return self.wrap(t)


def enumeration[T: DomainObject](name: str, names: Sequence[str], wrap: type[T]) -> ObjectSort[T]:
    """列挙型としてドメイン依存のソートを作る

    Args:
        name: ソート名 (Z3 では同名のデータ型が同じソートになるので，ドメインごとに一意にする)
        names: 対象の名前
        wrap: このソートの項を包む Python のクラス

    Returns:
        ドメイン依存のソート
    """
    sort, _ = z3.EnumSort(name, list(names))
    return ObjectSort(sort, wrap)


# ---------------------------------------------------------------------------
# 関数記号 (行動・フルエント)
# ---------------------------------------------------------------------------


@dataclass(frozen=True, eq=False)
class Signature:
    """行動またはフルエントの関数記号の宣言 (名前と引数のソート)

    Attributes:
        name: 関数記号の名前 (Z3 の構成子名になる)
        params: 引数のソート
    """

    name: str
    params: tuple[ObjectSort[DomainObject], ...] = ()


@dataclass(frozen=True, eq=False)
class FunctionSymbol:
    """Z3 データ型の 1 構成子に対応する関数記号 (行動・フルエント共通部分)

    Attributes:
        name: 関数記号の名前
        params: 引数のソート
        constructor: Z3 の構成子
        recognizer: Z3 の認識子 (``is_<name>``)
        accessors: Z3 のアクセサ (引数ごと)
    """

    name: str
    params: tuple[ObjectSort[DomainObject], ...]
    constructor: z3.FuncDeclRef
    recognizer: z3.FuncDeclRef
    accessors: tuple[z3.FuncDeclRef, ...]

    @property
    def arity(self) -> int:
        """引数の個数"""
        return len(self.params)

    def _apply(self, args: Sequence[DomainObject]) -> z3.DatatypeRef:
        """構成子を引数に適用した項を作る

        Args:
            args: 引数の項

        Returns:
            Z3 のデータ型の項 ``C(t1, ..., tn)``

        Raises:
            TypeError: 引数の個数かソートが宣言と合わないとき
        """
        if len(args) != self.arity:
            msg = f"{self.name} は {self.arity} 引数だが {len(args)} 個与えられた"
            raise TypeError(msg)
        for i, (arg, sort) in enumerate(zip(args, self.params, strict=True)):
            if not arg.expr.sort().eq(sort.sort):
                msg = f"{self.name} の第 {i + 1} 引数はソート {sort.name} だが {arg} が与えられた"
                raise TypeError(msg)
        return as_datatype_term(self.constructor(*(a.expr for a in args)))

    def _recognize(self, t: Term) -> Formula:
        """認識子 ``is_C(t)`` を作る

        Args:
            t: 項

        Returns:
            論理式 ``∃x1, ..., xn. t = C(x1, ..., xn)`` (Z3 の認識子)
        """
        return as_formula(self.recognizer(t.expr))

    def _arguments(self, t: Term) -> tuple[DomainObject, ...]:
        """アクセサで引数を取り出した項を作る

        Args:
            t: 項

        Returns:
            ``t = C(x1, ..., xn)`` のときの x1, ..., xn (Z3 のアクセサの適用)
        """
        return tuple(
            sort.lift(acc(t.expr)) for sort, acc in zip(self.params, self.accessors, strict=True)
        )

    def matches(self, t: Term) -> bool:
        """項がこの記号の構成子の適用かを，構文的に判定する

        Args:
            t: 項

        Returns:
            頂点がこの記号の構成子なら True
        """
        return t.expr.decl().eq(self.constructor)


@dataclass(frozen=True, eq=False)
class ActionSymbol(FunctionSymbol):
    """行動関数記号 (例: ``stack``). 呼び出すと行動の項を作る"""

    def __call__(self, *args: DomainObject) -> Action:
        """行動の項 ``A(t1, ..., tn)`` を作る

        Args:
            *args: 引数の項 (ソートは宣言どおり)

        Returns:
            行動の項
        """
        return Action(self._apply(args))

    def recognize(self, a: Action) -> Formula:
        """``∃x1, ..., xn. a = A(x1, ..., xn)`` を作る (Z3 の認識子 ``is_A(a)``)

        Args:
            a: 行動の項

        Returns:
            論理式
        """
        return self._recognize(a)

    def arguments(self, a: Action) -> tuple[DomainObject, ...]:
        """``a = A(x1, ..., xn)`` のときの x1, ..., xn を作る (Z3 のアクセサ)

        Args:
            a: 行動の項

        Returns:
            引数の項のタプル
        """
        return self._arguments(a)


@dataclass(frozen=True, eq=False)
class FluentSymbol(FunctionSymbol):
    """関係フルエントの関数記号 (例: ``clear``). 呼び出すとフルエントの項を作る"""

    def __call__(self, *args: DomainObject) -> Fluent:
        """フルエントの項 ``F(t1, ..., tn)`` を作る

        Args:
            *args: 引数の項 (ソートは宣言どおり)

        Returns:
            フルエントの項
        """
        return Fluent(self._apply(args))

    def recognize(self, p: Fluent) -> Formula:
        """``∃x1, ..., xn. p = F(x1, ..., xn)`` を作る (Z3 の認識子 ``is_F(p)``)

        Args:
            p: フルエントの項

        Returns:
            論理式
        """
        return self._recognize(p)

    def arguments(self, p: Fluent) -> tuple[DomainObject, ...]:
        """``p = F(x1, ..., xn)`` のときの x1, ..., xn を作る (Z3 のアクセサ)

        Args:
            p: フルエントの項

        Returns:
            引数の項のタプル
        """
        return self._arguments(p)


def _declare_symbols(
    sort_name: str, signatures: Sequence[Signature]
) -> tuple[
    z3.DatatypeSortRef,
    tuple[tuple[Signature, z3.FuncDeclRef, z3.FuncDeclRef, tuple[z3.FuncDeclRef, ...]], ...],
]:
    """関数記号の宣言から Z3 のデータ型を作る

    各記号が 1 つの構成子になる．アクセサ名は ``<記号名>_<番号>``

    Args:
        sort_name: データ型の名前
        signatures: 関数記号の宣言

    Returns:
        データ型と，各記号の (宣言, 構成子, 認識子, アクセサ) の組
    """
    dt = z3.Datatype(sort_name)
    for sig in signatures:
        dt.declare(sig.name, *((f"{sig.name}_{i + 1}", p.sort) for i, p in enumerate(sig.params)))
    sort = dt.create()
    parts = tuple(
        (
            sig,
            sort.constructor(i),
            sort.recognizer(i),
            tuple(sort.accessor(i, j) for j in range(len(sig.params))),
        )
        for i, sig in enumerate(signatures)
    )
    return sort, parts


# ---------------------------------------------------------------------------
# 言語
# ---------------------------------------------------------------------------


class SitCalcLanguage:
    """あるドメインの状況計算の言語 (ソートと特別な記号の集まり)

    Z3 では同名のデータ型が同じソートとして扱われるため，ソート名には
    ドメイン名を付ける (例: ``Situation_blocks``)

    Attributes:
        domain: ドメイン名 (Z3 のソート名の接尾辞)
        actions: 行動の関数記号 (名前 → 記号)
        fluents: 関係フルエントの関数記号 (名前 → 記号)
        action_sort: ソート action (Z3 のデータ型)
        fluent_sort: ソート fluent (Z3 のデータ型)
        situation_sort: ソート situation (Z3 のデータ型 ``S0 | do(Action, Situation)``)
        holds_decl: ``Holds : Fluent × Situation → Bool`` (未解釈関数)
        poss_decl: ``Poss : Action × Situation → Bool`` (未解釈関数)
        precedes_decl: ``⊏ : Situation × Situation → Bool`` (未解釈関数)
        executable_decl: ``Executable : Situation × Situation → Bool`` (未解釈関数)
    """

    def __init__(
        self,
        domain: str,
        actions: Sequence[Signature],
        fluents: Sequence[Signature],
    ) -> None:
        """行動とフルエントの関数記号から言語を作る

        Args:
            domain: ドメイン名 (Z3 のソート名の接尾辞になる)
            actions: 行動の関数記号の宣言
            fluents: 関係フルエントの関数記号の宣言
        """
        self.domain: str = domain

        # sort action
        self.action_sort, action_parts = _declare_symbols(f"Action_{domain}", actions)
        self.actions: dict[str, ActionSymbol] = {
            sig.name: ActionSymbol(sig.name, sig.params, c, r, acc)
            for sig, c, r, acc in action_parts
        }

        # sort fluent (関係フルエントを一階の対象として扱う, p.651)
        self.fluent_sort, fluent_parts = _declare_symbols(f"Fluent_{domain}", fluents)
        self.fluents: dict[str, FluentSymbol] = {
            sig.name: FluentSymbol(sig.name, sig.params, c, r, acc)
            for sig, c, r, acc in fluent_parts
        }

        # sort situation:  Situation ::= S0 | do(Action, Situation)
        # データ型なので，構成子の単射性 (16.62) と「状況は S0 から有限回の do で
        # 得られるものに限る」(16.63 の帰結, p.661–662) が Z3 の意味論で成り立つ
        sit = z3.Datatype(f"Situation_{domain}")
        sit.declare("S0")
        sit.declare("do", ("do_action", self.action_sort), ("do_situation", sit))
        self.situation_sort: z3.DatatypeSortRef = sit.create()
        self._s0_decl = self.situation_sort.constructor(0)
        self._do_decl = self.situation_sort.constructor(1)
        self._is_do = self.situation_sort.recognizer(1)
        self._do_action = self.situation_sort.accessor(1, 0)
        self._do_situation = self.situation_sort.accessor(1, 1)

        b = z3.BoolSort()
        # Holds(p, s), Poss(a, s): §16.1 p.651
        self.holds_decl: z3.FuncDeclRef = z3.Function(
            "Holds", self.fluent_sort, self.situation_sort, b
        )
        self.poss_decl: z3.FuncDeclRef = z3.Function(
            "Poss", self.action_sort, self.situation_sort, b
        )
        # s ⊏ s' (16.64)–(16.65), Executable(s, s') p.662
        self.precedes_decl: z3.FuncDeclRef = z3.Function(
            "Precedes", self.situation_sort, self.situation_sort, b
        )
        self.executable_decl: z3.FuncDeclRef = z3.Function(
            "Executable", self.situation_sort, self.situation_sort, b
        )

    # -- situation ---------------------------------------------------------

    @property
    def s0(self) -> Situation:
        """初期状況 S0"""
        return Situation(as_datatype_term(self._s0_decl()))

    def do(self, a: Action, s: Situation) -> Situation:
        """``do(a, s)``: 状況 s で行動 a を行った結果の状況を作る

        Args:
            a: 行動の項
            s: 状況の項

        Returns:
            状況の項 ``do(a, s)``
        """
        return Situation(as_datatype_term(self._do_decl(a.expr, s.expr)))

    def do_sequence(self, actions: Sequence[Action], s: Situation | None = None) -> Situation:
        """``do([a1, ..., an], s) = do(an, do(..., do(a1, s)...))`` を作る (p.662)

        Args:
            actions: 行動列 [a1, ..., an]
            s: 出発する状況 (省略すると S0)

        Returns:
            状況の項
        """
        result = self.s0 if s is None else s
        for a in actions:
            result = self.do(a, result)
        return result

    def is_s0(self, s: Situation) -> Formula:
        """``s = S0`` を作る

        Args:
            s: 状況の項

        Returns:
            論理式
        """
        return s.expr == self.s0.expr

    def is_do(self, s: Situation) -> Formula:
        """``∃a, s'. s = do(a, s')`` を作る (Z3 の認識子)

        Args:
            s: 状況の項

        Returns:
            論理式
        """
        return as_formula(self._is_do(s.expr))

    def do_action(self, s: Situation) -> Action:
        """``s = do(a, s')`` のときの a を作る (Z3 のアクセサ)

        Args:
            s: 状況の項

        Returns:
            行動の項
        """
        return Action(as_datatype_term(self._do_action(s.expr)))

    def do_situation(self, s: Situation) -> Situation:
        """``s = do(a, s')`` のときの s' を作る (Z3 のアクセサ)

        Args:
            s: 状況の項

        Returns:
            状況の項
        """
        return Situation(as_datatype_term(self._do_situation(s.expr)))

    def history(self, s: Situation) -> tuple[Action, ...]:
        """基礎的な状況項 ``do([a1, ..., an], S0)`` から行動列を取り出す

        状況と行動列の 1 対 1 対応 (p.662) を，構文的にたどる

        Args:
            s: S0 から do だけで作った状況項

        Returns:
            行動列 (a1, ..., an)

        Raises:
            ValueError: s が S0 から do で作った項でないとき (変数を含むなど)
        """
        acts: list[Action] = []
        cur = s
        while not cur.expr.eq(self.s0.expr):
            if not cur.expr.decl().eq(self._do_decl):
                msg = f"S0 から do で作られた状況項ではない: {s}"
                raise ValueError(msg)
            acts.append(Action(as_datatype_term(cur.expr.arg(0))))
            cur = Situation(as_datatype_term(cur.expr.arg(1)))
        return tuple(reversed(acts))

    # -- 特別な述語 ----------------------------------------------------------

    def holds(self, p: Fluent, s: Situation) -> Formula:
        """``Holds(p, s)``: フルエント p が状況 s で真，を作る

        Args:
            p: フルエントの項
            s: 状況の項

        Returns:
            論理式
        """
        return as_formula(self.holds_decl(p.expr, s.expr))

    def poss(self, a: Action, s: Situation) -> Formula:
        """``Poss(a, s)``: 行動 a が状況 s で実行可能，を作る

        Args:
            a: 行動の項
            s: 状況の項

        Returns:
            論理式
        """
        return as_formula(self.poss_decl(a.expr, s.expr))

    def precedes(self, s: Situation, s2: Situation) -> Formula:
        """``s ⊏ s'``: s' は s から空でない行動列で得られる，を作る (16.64)–(16.65)

        Args:
            s: 状況 s
            s2: 状況 s'

        Returns:
            論理式
        """
        return as_formula(self.precedes_decl(s.expr, s2.expr))

    def precedes_eq(self, s: Situation, s2: Situation) -> Formula:
        """``s ⊑ s'`` (``s ⊏ s' ∨ s = s'`` の略記, p.662) を作る

        Args:
            s: 状況 s
            s2: 状況 s'

        Returns:
            論理式
        """
        return z3.Or(self.precedes(s, s2), eq(s, s2))

    def executable(self, s: Situation, s2: Situation) -> Formula:
        """``Executable(s, s')``: s から s' への行動列が s で実行可能，を作る (p.662)

        Args:
            s: 状況 s
            s2: 状況 s'

        Returns:
            論理式
        """
        return as_formula(self.executable_decl(s.expr, s2.expr))

    # -- 変数 ---------------------------------------------------------------

    def situation_var(self, name: str) -> Situation:
        """ソート situation の変数を作る

        Args:
            name: 変数名

        Returns:
            状況の変数
        """
        return Situation(as_datatype_term(z3.Const(name, self.situation_sort)))

    def action_var(self, name: str) -> Action:
        """ソート action の変数を作る

        Args:
            name: 変数名

        Returns:
            行動の変数
        """
        return Action(as_datatype_term(z3.Const(name, self.action_sort)))

    def fluent_var(self, name: str) -> Fluent:
        """ソート fluent の変数を作る

        Args:
            name: 変数名

        Returns:
            フルエントの変数
        """
        return Fluent(as_datatype_term(z3.Const(name, self.fluent_sort)))

    # -- 基礎項の列挙 (可視化・モデル表示用) -----------------------------------

    def ground_actions(self) -> tuple[Action, ...]:
        """すべての基礎的な行動の項 (引数に対象を入れたもの) を返す

        Returns:
            行動の項のタプル (記号の宣言順，引数は対象の直積の順)
        """
        return tuple(
            sym(*args)
            for sym in self.actions.values()
            for args in product(*(p.constants() for p in sym.params))
        )

    def ground_fluents(self) -> tuple[Fluent, ...]:
        """すべての基礎的なフルエントの項を返す

        Returns:
            フルエントの項のタプル (記号の宣言順，引数は対象の直積の順)
        """
        return tuple(
            sym(*args)
            for sym in self.fluents.values()
            for args in product(*(p.constants() for p in sym.params))
        )

    def action_symbol_of(self, a: Action) -> ActionSymbol:
        """行動の項の関数記号を返す

        Args:
            a: 行動関数記号の適用である項

        Returns:
            その関数記号

        Raises:
            ValueError: a が行動関数記号の適用でないとき (変数など)
        """
        for sym in self.actions.values():
            if sym.matches(a):
                return sym
        msg = f"行動関数記号の適用ではない: {a}"
        raise ValueError(msg)

    def fluent_symbol_of(self, p: Fluent) -> FluentSymbol:
        """フルエントの項の関数記号を返す

        Args:
            p: フルエント関数記号の適用である項

        Returns:
            その関数記号

        Raises:
            ValueError: p がフルエント関数記号の適用でないとき (変数など)
        """
        for sym in self.fluents.values():
            if sym.matches(p):
                return sym
        msg = f"フルエント関数記号の適用ではない: {p}"
        raise ValueError(msg)

    def lift_action(self, e: z3.ExprRef) -> Action:
        """ソート action の Z3 の式を，行動の項として包む

        Args:
            e: Z3 の式 (モデルの評価結果など)

        Returns:
            行動の項

        Raises:
            TypeError: e がソート action の項でないとき
        """
        t = as_datatype_term(e)
        if not t.sort().eq(self.action_sort):
            msg = f"ソート action の項ではない: {t}"
            raise TypeError(msg)
        return Action(t)
