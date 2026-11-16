"""公理の種類 (§16.3 の基本行動理論を構成する部品)

本書 p.664 の基本行動理論 D = Σ ∪ D_ss ∪ D_ap ∪ D_una ∪ D_S0 の各要素を表すクラス:

==========================  ===================================================
本書                         この実装
==========================  ===================================================
後継状態公理 (16.66)         :class:`SuccessorStateAxiom`
行動前提条件公理 (p.663)     :class:`ActionPreconditionAxiom`
D_S0 の文 (p.664)            :class:`InitialAxiom`, :class:`InitialFluentDefinition`
Σ, D_una などの一般の文       :class:`Sentence`
(16.63) 二階の帰納法公理     :class:`SecondOrderAxiom` (一階の Z3 には渡せない)
==========================  ===================================================

本書の慣習 (p.651 "all free variables are assumed to be universally quantified")
どおり，公理は自由変数を明示的に持ち，:attr:`Axiom.formula` で全称閉包を返す

uniform な式 (p.662–663) の判定 :func:`uniform_violations` もここに置く
"""

from abc import ABC, abstractmethod
from collections.abc import Iterator, Sequence
from dataclasses import dataclass

import z3

from sc.sitcalc.language import (
    Action,
    ActionSymbol,
    DomainObject,
    Fluent,
    FluentSymbol,
    Formula,
    SitCalcLanguage,
    Situation,
    Term,
    as_datatype_term,
    as_formula,
    eq,
    is_variable,
)
from sc.sitcalc.pretty import show

# ---------------------------------------------------------------------------
# 式の操作
# ---------------------------------------------------------------------------


def forall(variables: Sequence[Term], body: Formula) -> Formula:
    """全称閉包 ``∀x⃗. body`` を作る

    Args:
        variables: 量化する変数 x⃗
        body: 本体

    Returns:
        全称閉包 (変数がなければ body そのもの)
    """
    if not variables:
        return body
    return z3.ForAll([v.expr for v in variables], body)


def instantiate(body: Formula, variables: Sequence[Term], terms: Sequence[Term]) -> Formula:
    """``body`` の自由変数 ``variables`` を ``terms`` で同時に置き換える

    Z3 の束縛変数は de Bruijn 添字なので，置き換えで変数の捕獲は起きない

    Args:
        body: 論理式
        variables: 置き換える自由変数
        terms: 代わりに入れる項 (variables と同じ順)

    Returns:
        置き換えた論理式

    Raises:
        ValueError: variables と terms の個数が違うとき
    """
    if len(variables) != len(terms):
        msg = f"変数 {len(variables)} 個に対して項が {len(terms)} 個"
        raise ValueError(msg)
    if not variables:
        return body
    pairs = tuple((v.expr, t.expr) for v, t in zip(variables, terms, strict=True))
    return as_formula(z3.substitute(body, *pairs))


def subterms(e: z3.ExprRef) -> Iterator[z3.ExprRef]:
    """式のすべての部分式を前順にたどる (量化子の本体も含む)

    Args:
        e: Z3 の式

    Yields:
        e 自身とその部分式 (量化子の本体中の束縛変数は ``Var(i)`` のまま)
    """
    yield e
    if isinstance(e, z3.QuantifierRef):
        yield from subterms(e.body())
    elif z3.is_app(e):
        for c in e.children():
            yield from subterms(c)


def uniform_violations(language: SitCalcLanguage, phi: Formula, sigma: Situation) -> list[str]:
    """式 φ が状況項 σ で uniform でない理由の一覧 (空なら uniform). p.662–663

    本書の条件 (p.662–663):

    - it does not contain any quantification over situation;
    - it does not mention any variables for relational fluents;
    - it does not mention any situation term other than σ;
    - it does not mention any predicate that has a situation argument other than Holds;
    - it does not mention any function that has a situation argument unless the function
      is a functional fluent. (この実装は関数フルエントを扱わないので「なし」)

    Args:
        language: 言語
        phi: 調べる式
        sigma: 状況項 σ

    Returns:
        uniform でない理由の一覧 (重複なし，整列済み)．空なら uniform
    """
    reasons: set[str] = set()
    sit_sort = language.situation_sort
    fluent_sort = language.fluent_sort
    for e in subterms(phi):
        if isinstance(e, z3.QuantifierRef):
            for i in range(e.num_vars()):
                if e.var_sort(i).eq(sit_sort):
                    reasons.add(f"状況について量化している: {e.var_name(i)}")
                if e.var_sort(i).eq(fluent_sort):
                    reasons.add(f"関係フルエントの変数を量化している: {e.var_name(i)}")
            continue
        if z3.is_var(e) or not z3.is_app(e):
            continue
        sort = e.sort()
        if sort.eq(sit_sort) and not e.eq(sigma.expr):
            reasons.add(f"{show(sigma.expr)} 以外の状況項を含む: {show(e)}")
        if sort.eq(fluent_sort) and is_variable(Fluent(as_datatype_term(e))):
            reasons.add(f"関係フルエントの変数を含む: {show(e)}")
        situation_argument = any(c.sort().eq(sit_sort) for c in e.children())
        if situation_argument and not sort.eq(sit_sort) and not e.decl().eq(language.holds_decl):
            reasons.add(f"Holds 以外の記号が状況引数を持つ: {e.decl().name()}")
    return sorted(reasons)


def _require_uniform(language: SitCalcLanguage, phi: Formula, sigma: Situation, what: str) -> None:
    """式が状況項 σ で uniform であることを確かめる

    Args:
        language: 言語
        phi: 調べる式
        sigma: 状況項 σ
        what: エラーメッセージに使う，式の説明

    Raises:
        ValueError: uniform でないとき (理由をメッセージに含める)
    """
    reasons = uniform_violations(language, phi, sigma)
    if reasons:
        msg = f"{what} が {show(sigma.expr)} で uniform でない: " + "; ".join(reasons)
        raise ValueError(msg)


def _require_variables(params: Sequence[Term], what: str) -> None:
    """項がすべて変数で，互いに異なることを確かめる

    Args:
        params: 調べる項
        what: エラーメッセージに使う，公理の説明

    Raises:
        ValueError: 変数でない項があるか，同じ変数が重複しているとき
    """
    for v in params:
        if not is_variable(v):
            msg = f"{what} の引数は変数でなければならない: {v}"
            raise ValueError(msg)
    if len({v.expr.hash() for v in params}) != len(params):
        msg = f"{what} の引数の変数が重複している: {[str(v) for v in params]}"
        raise ValueError(msg)


# ---------------------------------------------------------------------------
# 公理
# ---------------------------------------------------------------------------


@dataclass(frozen=True, eq=False, kw_only=True)
class Axiom(ABC):
    """公理 (一階の文) の基底クラス

    Attributes:
        ref: 本書での出典 (式番号やページ, 例: ``"(16.7)"``, ``"p.654"``)
        note: 補足説明 (日本語)

    """

    ref: str
    note: str = ""

    @property
    @abstractmethod
    def formula(self) -> Formula:
        """Z3 に渡す一階の文 (自由変数の全称閉包)"""

    def statement(self) -> str:
        """本書の書き方 (自由変数は暗黙に全称量化) での表示

        Returns:
            表示用の文字列
        """
        return show(self.formula)


@dataclass(frozen=True, eq=False, kw_only=True)
class Sentence(Axiom):
    """一般の一階の文 (Σ, D_una, 状態制約など)

    Attributes:
        sentence: 一階の文 (Z3 の式)
        display: 表示用の文字列 (None なら ``sentence`` を本書の記法で表示)
    """

    sentence: Formula
    display: str | None = None

    @property
    def formula(self) -> Formula:
        """文そのもの"""
        return self.sentence

    def statement(self) -> str:
        """表示用の文字列 (``display`` があればそれを使う)

        Returns:
            表示用の文字列
        """
        return self.display if self.display is not None else show(self.sentence)


@dataclass(frozen=True, eq=False, kw_only=True)
class SecondOrderAxiom:
    """二階の公理 (Z3 = 一階の自動証明器には渡せないので，表示と説明のみ)

    本書の (16.63) ∀P.[P(S0) ∧ ∀a, s.P(s) ⊃ P(do(a, s))] ⊃ ∀s P(s) がこれにあたる
    特定の P についての一階の具体例は ``BasicActionTheory.induction_instance`` で作る

    Attributes:
        ref: 本書での出典
        text: 公理の表示用の文字列
        note: 補足説明
    """

    ref: str
    text: str
    note: str = ""


@dataclass(frozen=True, eq=False, kw_only=True)
class SuccessorStateAxiom(Axiom):
    """後継状態公理 (successor state axiom) (16.66)

        F(x1, ..., xn, do(a, s)) ≡ Φ_F(x1, ..., xn, a, s)

    Φ_F は s で uniform で，自由変数は x1, ..., xn, a, s のみ (p.663)

    Attributes:
        language: 言語
        fluent: フルエントの関数記号 F
        params: 変数 x1, ..., xn
        action: 変数 a
        situation: 変数 s
        phi: Φ_F

    """

    language: SitCalcLanguage
    fluent: FluentSymbol
    params: tuple[DomainObject, ...]
    action: Action
    situation: Situation
    phi: Formula

    def __post_init__(self) -> None:
        """引数が変数であることと，Φ_F が s で uniform であることを検査する

        Raises:
            ValueError: 引数が変数でない・重複している，または Φ_F が uniform でないとき
        """
        _require_variables(
            [*self.params, self.action, self.situation], f"{self.fluent.name} の SSA"
        )
        _require_uniform(self.language, self.phi, self.situation, f"{self.fluent.name} の Φ_F")

    @property
    def variables(self) -> tuple[Term, ...]:
        """自由変数 x⃗, a, s"""
        return (*self.params, self.action, self.situation)

    @property
    def lhs(self) -> Formula:
        """左辺 ``F(x⃗, do(a, s))``"""
        lang = self.language
        return lang.holds(self.fluent(*self.params), lang.do(self.action, self.situation))

    @property
    def formula(self) -> Formula:
        """``∀x⃗, a, s. F(x⃗, do(a, s)) ≡ Φ_F(x⃗, a, s)``"""
        return forall(self.variables, self.lhs == self.phi)

    def statement(self) -> str:
        """``F(x⃗, do(a, s)) ≡ Φ_F(x⃗, a, s)`` (自由変数は暗黙に全称量化)

        Returns:
            表示用の文字列
        """
        return f"{show(self.lhs)} ≡ {show(self.phi)}"

    def instantiate(
        self, args: Sequence[DomainObject], action: Action, situation: Situation
    ) -> Formula:
        """``Φ_F(t⃗, α, σ)``: 回帰 (§16.3 p.665) で ``F(t⃗, do(α, σ))`` を置き換える式

        Args:
            args: x⃗ に入れる項 t⃗
            action: a に入れる行動の項 α
            situation: s に入れる状況の項 σ

        Returns:
            論理式 ``Φ_F(t⃗, α, σ)``
        """
        return instantiate(self.phi, self.variables, [*args, action, situation])


@dataclass(frozen=True, eq=False, kw_only=True)
class ActionPreconditionAxiom(Axiom):
    """行動前提条件公理 (action precondition axiom) (p.663)

        Poss(A(x1, ..., xn), s) ≡ Π_A(x1, ..., xn, s)

    Π_A は s で uniform で，自由変数は x1, ..., xn, s のみ

    Attributes:
        language: 言語
        action_symbol: 行動の関数記号 A
        params: 変数 x1, ..., xn
        situation: 変数 s
        pi: Π_A
    """

    language: SitCalcLanguage
    action_symbol: ActionSymbol
    params: tuple[DomainObject, ...]
    situation: Situation
    pi: Formula

    def __post_init__(self) -> None:
        """引数が変数であることと，Π_A が s で uniform であることを検査する

        Raises:
            ValueError: 引数が変数でない・重複している，または Π_A が uniform でないとき
        """
        _require_variables([*self.params, self.situation], f"Poss({self.action_symbol.name})")
        _require_uniform(
            self.language, self.pi, self.situation, f"{self.action_symbol.name} の Π_A"
        )

    @property
    def variables(self) -> tuple[Term, ...]:
        """自由変数 x⃗, s"""
        return (*self.params, self.situation)

    @property
    def lhs(self) -> Formula:
        """左辺 ``Poss(A(x⃗), s)``"""
        return self.language.poss(self.action_symbol(*self.params), self.situation)

    @property
    def formula(self) -> Formula:
        """``∀x⃗, s. Poss(A(x⃗), s) ≡ Π_A(x⃗, s)``"""
        return forall(self.variables, self.lhs == self.pi)

    def statement(self) -> str:
        """``Poss(A(x⃗), s) ≡ Π_A(x⃗, s)``

        Returns:
            表示用の文字列
        """
        return f"{show(self.lhs)} ≡ {show(self.pi)}"

    def instantiate(self, args: Sequence[DomainObject], situation: Situation) -> Formula:
        """``Π_A(t⃗, σ)`` を作る

        Args:
            args: x⃗ に入れる項 t⃗
            situation: s に入れる状況の項 σ

        Returns:
            論理式 ``Π_A(t⃗, σ)``
        """
        return instantiate(self.pi, self.variables, [*args, situation])


@dataclass(frozen=True, eq=False, kw_only=True)
class InitialAxiom(Axiom):
    """D_S0 の文: S0 で uniform な文 (p.664)

    Attributes:
        language: 言語
        sentence: S0 で uniform な文
    """

    language: SitCalcLanguage
    sentence: Formula

    def __post_init__(self) -> None:
        """S0 で uniform であることを検査する

        Raises:
            ValueError: 文が S0 で uniform でないとき
        """
        _require_uniform(self.language, self.sentence, self.language.s0, "D_S0 の文")

    @property
    def formula(self) -> Formula:
        """文そのもの"""
        return self.sentence


@dataclass(frozen=True, eq=False, kw_only=True)
class InitialFluentDefinition(Axiom):
    """D_S0 の文のうち，あるフルエントの S0 での真偽を完全に定めるもの

        ∀x⃗. F(x⃗, S0) ≡ ψ_F(x⃗)

    全フルエントについてこの形の文があるとき D_S0 は「完全」で
    D の Holds は状況の木の上で一意に決まる (帰納法 (16.63) による)
    このとき ``BasicActionTheory.compile`` で再帰関数にコンパイルできる

    Attributes:
        language: 言語
        fluent: フルエントの関数記号 F
        params: 変数 x⃗
        body: ψ_F(x⃗) (S0 で uniform)
    """

    language: SitCalcLanguage
    fluent: FluentSymbol
    params: tuple[DomainObject, ...]
    body: Formula

    def __post_init__(self) -> None:
        """引数が変数であることと，S0 で uniform であることを検査する

        Raises:
            ValueError: 引数が変数でない・重複している，または ψ_F が uniform でないとき
        """
        _require_variables(self.params, f"{self.fluent.name}(…, S0) の定義")
        _require_uniform(self.language, self.body, self.language.s0, f"{self.fluent.name} の初期値")

    @property
    def lhs(self) -> Formula:
        """``F(x⃗, S0)``"""
        return self.language.holds(self.fluent(*self.params), self.language.s0)

    @property
    def formula(self) -> Formula:
        """``∀x⃗. F(x⃗, S0) ≡ ψ_F(x⃗)``"""
        return forall(self.params, self.lhs == self.body)

    def statement(self) -> str:
        """``F(x⃗, S0) ≡ ψ_F(x⃗)``

        Returns:
            表示用の文字列
        """
        return f"{show(self.lhs)} ≡ {show(self.body)}"

    def instantiate(self, args: Sequence[DomainObject]) -> Formula:
        """``ψ_F(t⃗)`` を作る

        Args:
            args: x⃗ に入れる項 t⃗

        Returns:
            論理式 ``ψ_F(t⃗)``
        """
        return instantiate(self.body, self.params, args)


def closed_initial_database(
    language: SitCalcLanguage,
    true_fluents: Sequence[Fluent],
    *,
    ref: str,
    note: str = "",
) -> tuple[InitialFluentDefinition, ...]:
    """「列挙したフルエントだけが S0 で真」という完全な D_S0 を作る (閉世界仮定)

    各フルエント記号 F について ``∀x⃗. F(x⃗, S0) ≡ ⋁ (x⃗ = c⃗)`` を作る
    ここで c⃗ は true_fluents に現れる F(c⃗) の引数

    Args:
        language: 言語
        true_fluents: S0 で真なフルエント (基礎項)
        ref: 各文の出典
        note: 各文の補足説明

    Returns:
        フルエント記号ごとの S0 での定義 (完全な D_S0)
    """
    result: list[InitialFluentDefinition] = []
    for sym in language.fluents.values():
        params = tuple(p.var(f"x{i + 1}") for i, p in enumerate(sym.params))
        cases: list[Formula] = []
        for f in true_fluents:
            if not sym.matches(f):
                continue
            args = [DomainObject(as_datatype_term(c)) for c in f.expr.children()]
            cases.append(
                z3.And(*(eq(x, c) for x, c in zip(params, args, strict=True)))
                if args
                else z3.BoolVal(True)
            )
        body = z3.Or(*cases) if cases else z3.BoolVal(False)
        result.append(
            InitialFluentDefinition(
                language=language, fluent=sym, params=params, body=body, ref=ref, note=note
            )
        )
    return tuple(result)
