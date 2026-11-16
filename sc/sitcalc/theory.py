"""基本行動理論 (basic action theory) (§16.3, p.664)

    D = Σ ∪ D_ss ∪ D_ap ∪ D_una ∪ D_S0

- Σ     : 基礎公理 (foundational axioms) (16.62)–(16.65)
- D_ss  : 後継状態公理 (successor state axioms) (16.66)
- D_ap  : 行動前提条件公理 (action precondition axioms) (p.663)
- D_una : 行動についての一意名公理 (unique names axioms) (p.656, p.664)
- D_S0  : S0 で uniform な文 (初期状況についての知識) (p.664)

Z3 での扱い:

- Σ の (16.62) と D_una は Z3 データ型の意味論 (構成子は単射で互いに異なる) で
  自動的に成り立つ．理論の「見える化」のため，一階の文としても列挙する
- Σ の (16.63) は二階の帰納法公理で，一階の Z3 には渡せない．特定の性質 P に
  ついての一階の具体例を :meth:`BasicActionTheory.induction_instance` で作れる
  なお Z3 のデータ型の意味論 (状況はすべて S0 からの有限の do の列) は (16.63) の
  標準モデルと一致するが，Z3 は帰納法を自動では使わない (``examples/induction.py``)
- (16.64)–(16.65) の ⊏ と p.662 の Executable は未解釈関数と公理で表す

二つの使い方:

1. :meth:`BasicActionTheory.entails` — D ⊨ φ を一階の帰結として判定する (本書どおり)
2. :meth:`BasicActionTheory.compile` — D_S0 が完全なとき，Holds と Poss を
   状況についての再帰関数にコンパイルする．モデルを探す問題 (プランニング) は
   1 の形だと量化子のせいで Z3 が unknown を返しやすいので，こちらを使う
"""

from collections.abc import Callable, Sequence
from dataclasses import dataclass

import z3

from sc.sitcalc.axioms import (
    ActionPreconditionAxiom,
    Axiom,
    InitialAxiom,
    InitialFluentDefinition,
    SecondOrderAxiom,
    Sentence,
    SuccessorStateAxiom,
    forall,
)
from sc.sitcalc.language import (
    Action,
    ActionSymbol,
    DomainObject,
    Fluent,
    FluentSymbol,
    Formula,
    SitCalcLanguage,
    Situation,
    as_formula,
    eq,
    ne,
)
from sc.sitcalc.simplify import eliminate_constructor_quantifiers
from sc.sitcalc.solving import DEFAULT_TIMEOUT_MS, Entailment, SatResult, entails, satisfiable

type InitialSentence = InitialAxiom | InitialFluentDefinition


@dataclass(frozen=True, eq=False)
class AxiomGroup:
    """基本行動理論の構成要素 (Σ, D_ss, ...) の 1 つ

    Attributes:
        symbol: 本書での記号 (``"Σ"``, ``"D_ss"`` など)
        title: 日本語名と英語名
        ref: 本書での出典
        axioms: 一階の公理
        second_order: 二階の公理 (表示のみ)
        note: 補足

    """

    symbol: str
    title: str
    ref: str
    axioms: tuple[Axiom, ...]
    second_order: tuple[SecondOrderAxiom, ...] = ()
    note: str = ""


class BasicActionTheory:
    """基本行動理論 D = Σ ∪ D_ss ∪ D_ap ∪ D_una ∪ D_S0 (p.664)

    Attributes:
        name: 理論の名前 (表示用)
        language: 言語
        d_ss: D_ss: 後継状態公理
        d_ap: D_ap: 行動前提条件公理
        d_s0: D_S0: 初期状況の公理
    """

    def __init__(
        self,
        *,
        name: str,
        language: SitCalcLanguage,
        d_ss: Sequence[SuccessorStateAxiom],
        d_ap: Sequence[ActionPreconditionAxiom],
        d_s0: Sequence[InitialSentence],
    ) -> None:
        """各構成要素から理論を作り，形式を検査する

        Args:
            name: 理論の名前 (表示用)
            language: 言語
            d_ss: 後継状態公理 (フルエント記号ごとに高々 1 つ)
            d_ap: 行動前提条件公理 (行動記号ごとに高々 1 つ)
            d_s0: 初期状況の公理

        Raises:
            ValueError: 同じ記号に公理が 2 つある，別の言語の公理が混ざっている，など
        """
        self.name = name
        self.language = language
        self.d_ss: tuple[SuccessorStateAxiom, ...] = tuple(d_ss)
        self.d_ap: tuple[ActionPreconditionAxiom, ...] = tuple(d_ap)
        self.d_s0: tuple[InitialSentence, ...] = tuple(d_s0)
        self._validate()
        self._compiled: CompiledTheory | None = None

    def _validate(self) -> None:
        """公理が同じ言語のもので，記号ごとに高々 1 つであることを確かめる

        Raises:
            ValueError: 別の言語の公理がある，または同じ記号に公理が 2 つあるとき
        """
        seen_f: set[str] = set()
        for ax in self.d_ss:
            if ax.language is not self.language:
                msg = f"SSA {ax.fluent.name} は別の言語のもの"
                raise ValueError(msg)
            if ax.fluent.name in seen_f:
                msg = f"フルエント {ax.fluent.name} の SSA が複数ある"
                raise ValueError(msg)
            seen_f.add(ax.fluent.name)
        seen_a: set[str] = set()
        for ap in self.d_ap:
            if ap.language is not self.language:
                msg = f"Poss({ap.action_symbol.name}) は別の言語のもの"
                raise ValueError(msg)
            if ap.action_symbol.name in seen_a:
                msg = f"行動 {ap.action_symbol.name} の前提条件公理が複数ある"
                raise ValueError(msg)
            seen_a.add(ap.action_symbol.name)
        for ini in self.d_s0:
            if ini.language is not self.language:
                msg = "D_S0 に別の言語の文がある"
                raise ValueError(msg)

    # -- 構成要素の取り出し ----------------------------------------------------

    def ssa_for(self, fluent: FluentSymbol) -> SuccessorStateAxiom:
        """フルエント記号の後継状態公理を返す

        Args:
            fluent: フルエントの関数記号

        Returns:
            その記号の後継状態公理

        Raises:
            KeyError: その記号の後継状態公理がないとき
        """
        for ax in self.d_ss:
            if ax.fluent is fluent:
                return ax
        msg = f"フルエント {fluent.name} の SSA がない"
        raise KeyError(msg)

    def precondition_for(self, action: ActionSymbol) -> ActionPreconditionAxiom | None:
        """行動記号の前提条件公理を返す

        Args:
            action: 行動の関数記号

        Returns:
            前提条件公理．なければ None (そのとき Poss は無制約)
        """
        for ap in self.d_ap:
            if ap.action_symbol is action:
                return ap
        return None

    def initial_definition_for(self, fluent: FluentSymbol) -> InitialFluentDefinition | None:
        """フルエント記号の S0 での定義 (完全な D_S0 の一部) を返す

        Args:
            fluent: フルエントの関数記号

        Returns:
            S0 での定義．なければ None
        """
        for ini in self.d_s0:
            if isinstance(ini, InitialFluentDefinition) and ini.fluent is fluent:
                return ini
        return None

    def sigma(self) -> AxiomGroup:
        """Σ: 基礎公理 (16.62)–(16.65) を返す

        Returns:
            (16.62), (16.64), (16.65) の一階の文と，二階の (16.63) (表示のみ)
        """
        lang = self.language
        a, a2 = lang.action_var("a"), lang.action_var("a'")
        s, s2 = lang.situation_var("s"), lang.situation_var("s'")
        return AxiomGroup(
            symbol="Σ",
            title="基礎公理 (foundational axioms)",
            ref="(16.62)–(16.65)",
            axioms=(
                Sentence(
                    ref="(16.62)",
                    sentence=forall(
                        [a, s, a2, s2],
                        z3.Implies(
                            eq(lang.do(a, s), lang.do(a2, s2)), z3.And(eq(a, a2), eq(s, s2))
                        ),
                    ),
                    note="do の単射性。Z3 データ型の構成子は単射なので自動的に成り立つ",
                ),
                Sentence(
                    ref="(16.64)",
                    sentence=forall([s], z3.Not(lang.precedes(s, lang.s0))),
                    display="¬ s ⊏ S0",
                ),
                Sentence(
                    ref="(16.65)",
                    sentence=forall(
                        [s, a, s2],
                        lang.precedes(s, lang.do(a, s2)) == lang.precedes_eq(s, s2),
                    ),
                    display="s ⊏ do(a, s') ≡ s ⊑ s'",
                ),
            ),
            second_order=(
                SecondOrderAxiom(
                    ref="(16.63)",
                    text="∀P.[P(S0) ∧ ∀a, s.P(s) ⊃ P(do(a, s))] ⊃ ∀s P(s)",
                    note=(
                        "二階の帰納法公理。Z3 には渡せない (特定の P の具体例は induction_instance)"
                    ),
                ),
            ),
        )

    def definitions(self) -> AxiomGroup:
        """Executable の定義 (p.662) を，本書の不備を直した形で返す

        本書の定義:

            Executable(s, s),
            Executable(s, do(a, s')) ≡ Poss(a, s') ∧ Executable(s, s')

        は，2 つ目に s = do(a, s') を代入すると左辺が Executable(s, s) = 真になり
        ¬Poss(a, s') の行動が 1 つでもあると矛盾する (``examples/blocks_world.py``
        で Z3 により確認)．そこで 2 つ目を s ⊏ do(a, s') のときに限る

        Returns:
            Executable の定義の 2 つの文
        """
        lang = self.language
        a = lang.action_var("a")
        s, s2 = lang.situation_var("s"), lang.situation_var("s'")
        return AxiomGroup(
            symbol="Exec",
            title="Executable の定義 (定義による拡張)",
            ref="p.662",
            axioms=(
                Sentence(
                    ref="p.662",
                    sentence=forall([s], lang.executable(s, s)),
                    display="Executable(s, s)",
                ),
                Sentence(
                    ref="p.662 (修正)",
                    sentence=forall(
                        [s, a, s2],
                        z3.Implies(
                            lang.precedes(s, lang.do(a, s2)),
                            lang.executable(s, lang.do(a, s2))
                            == z3.And(lang.poss(a, s2), lang.executable(s, s2)),
                        ),
                    ),
                    display=(
                        "s ⊏ do(a, s') ⊃ "
                        "[Executable(s, do(a, s')) ≡ Poss(a, s') ∧ Executable(s, s')]"
                    ),
                    note="本書の定義に前提 s ⊏ do(a, s') を補った (本書のままだと矛盾する)",
                ),
            ),
        )

    def book_executable_definition(self) -> tuple[Formula, ...]:
        """本書 p.662 の Executable の定義を，そのままの形で返す (矛盾の確認用)

        Returns:
            本書のままの 2 つの文 (全称閉包)
        """
        lang = self.language
        a = lang.action_var("a")
        s, s2 = lang.situation_var("s"), lang.situation_var("s'")
        return (
            forall([s], lang.executable(s, s)),
            forall(
                [s, a, s2],
                lang.executable(s, lang.do(a, s2))
                == z3.And(lang.poss(a, s2), lang.executable(s, s2)),
            ),
        )

    def d_una(self) -> AxiomGroup:
        """D_una: 行動の一意名公理 (p.656)

        - 各 n 引数の行動 A: A(x1, ..., xn) = A(y1, ..., yn) ⊃ x1 = y1 ∧ ... ∧ xn = yn
        - 異なる行動 A, A': A(x1, ..., xn) ≠ A'(y1, ..., ym)

        Returns:
            一意名公理の文
        """
        syms = list(self.language.actions.values())
        axioms: list[Axiom] = []
        for sym in syms:
            if sym.arity == 0:
                continue
            xs = _params(sym, "x")
            ys = _params(sym, "y")
            axioms.append(
                Sentence(
                    ref="p.656",
                    sentence=forall(
                        [*xs, *ys],
                        z3.Implies(
                            eq(sym(*xs), sym(*ys)),
                            z3.And(*(eq(x, y) for x, y in zip(xs, ys, strict=True))),
                        ),
                    ),
                )
            )
        for i, sym in enumerate(syms):
            for other in syms[i + 1 :]:
                xs = _params(sym, "x")
                ys = _params(other, "y")
                axioms.append(
                    Sentence(ref="p.656", sentence=forall([*xs, *ys], ne(sym(*xs), other(*ys))))
                )
        return AxiomGroup(
            symbol="D_una",
            title="一意名公理 (unique names axioms for actions)",
            ref="p.656, p.664",
            axioms=tuple(axioms),
            note="Z3 データ型の構成子は単射かつ互いに異なるので、すべて自動的に成り立つ",
        )

    def groups(self) -> tuple[AxiomGroup, ...]:
        """D = Σ ∪ D_ss ∪ D_ap ∪ D_una ∪ D_S0 の各要素 (と Executable の定義) を返す

        Returns:
            構成要素のタプル (本書の並び順)
        """
        return (
            self.sigma(),
            AxiomGroup("D_ss", "後継状態公理 (successor state axioms)", "(16.66)", self.d_ss),
            AxiomGroup("D_ap", "行動前提条件公理 (action precondition axioms)", "p.663", self.d_ap),
            self.d_una(),
            AxiomGroup("D_S0", "初期状況の公理 (initial database)", "p.664", self.d_s0),
            self.definitions(),
        )

    def axioms(self) -> tuple[Formula, ...]:
        """D の一階の部分 (と Executable の定義) をすべて Z3 の式として返す

        Returns:
            公理の全称閉包のタプル
        """
        return tuple(ax.formula for g in self.groups() for ax in g.axioms)

    # -- 推論 ---------------------------------------------------------------

    def entails(
        self, phi: Formula, *, timeout_ms: int = DEFAULT_TIMEOUT_MS, expand_finite: bool = False
    ) -> Entailment:
        """``D ⊨ φ`` を判定する

        Args:
            phi: 論理式
            timeout_ms: Z3 の制限時間 (ミリ秒)
            expand_finite: 列挙型の量化子を展開してから解くか (:func:`sc.sitcalc.solving.entails`)

        Returns:
            判定結果
        """
        return entails(self.axioms(), phi, timeout_ms=timeout_ms, expand_finite=expand_finite)

    def relative_satisfiability(self, *, timeout_ms: int = DEFAULT_TIMEOUT_MS) -> SatResult:
        """定理 16.1 (Pirri–Reiter): D が充足可能 ⟺ D_una ∪ D_S0 が充足可能

        右辺 (D_una ∪ D_S0) の充足可能性を判定する

        Args:
            timeout_ms: Z3 の制限時間 (ミリ秒)

        Returns:
            D_una ∪ D_S0 の充足可能性 (定理 16.1 により D の充足可能性と一致)
        """
        formulas = [ax.formula for ax in self.d_una().axioms] + [ini.formula for ini in self.d_s0]
        return satisfiable(formulas, timeout_ms=timeout_ms)

    def induction_instance(self, prop: Callable[[Situation], Formula]) -> Formula:
        """(16.63) の P を prop に特殊化した一階の文

        [P(S0) ∧ ∀a, s. P(s) ⊃ P(do(a, s))] ⊃ ∀s. P(s)

        Args:
            prop: 性質 P (状況を受け取って論理式を返す)

        Returns:
            一階の文 ``[P(S0) ∧ ∀a, s. P(s) ⊃ P(do(a, s))] ⊃ ∀s. P(s)``
        """
        lang = self.language
        a, s = lang.action_var("a"), lang.situation_var("s")
        return z3.Implies(
            z3.And(prop(lang.s0), forall([a, s], z3.Implies(prop(s), prop(lang.do(a, s))))),
            forall([s], prop(s)),
        )

    # -- 場合分けによる Φ_F, Π_A の取り出し ------------------------------------

    def holds_cases(self, p: Fluent, a: Action, s: Situation) -> Formula:
        """``Holds(p, do(a, s))`` と同値な式 (p の構成子で場合分けした Φ_F)

        フルエントのデータ型は領域閉包を満たす (p はいずれかの F(x⃗) に等しい) ので
        D_ss から ``∀p, a, s. Holds(p, do(a, s)) ≡ holds_cases(p, a, s)`` が従う

        Args:
            p: フルエントの項 (変数や Var でもよい)
            a: 行動の項
            s: 状況の項

        Returns:
            ``if is_F1(p) then Φ_F1(…) else if … else Φ_Fn(…)``
        """
        cases = [
            (sym.recognize(p), self.ssa_for(sym).instantiate(sym.arguments(p), a, s))
            for sym in self.language.fluents.values()
        ]
        return _if_chain(cases)

    def poss_cases(self, a: Action, s: Situation) -> Formula:
        """``Poss(a, s)`` と同値な式 (a の構成子で場合分けした Π_A)

        Args:
            a: 行動の項 (変数や Var でもよい)
            s: 状況の項

        Returns:
            ``if is_A1(a) then Π_A1(…) else if … else Π_An(…)``

        Raises:
            ValueError: 前提条件公理のない行動記号があるとき
        """
        cases: list[tuple[Formula, Formula]] = []
        for sym in self.language.actions.values():
            ap = self.precondition_for(sym)
            if ap is None:
                msg = f"行動 {sym.name} の前提条件公理がないので Poss を定義できない"
                raise ValueError(msg)
            cases.append((sym.recognize(a), ap.instantiate(sym.arguments(a), s)))
        return _if_chain(cases)

    def initial_cases(self, p: Fluent) -> Formula:
        """``Holds(p, S0)`` と同値な式 (完全な D_S0 のとき)

        Args:
            p: フルエントの項 (変数や Var でもよい)

        Returns:
            ``if is_F1(p) then ψ_F1(…) else if … else ψ_Fn(…)``

        Raises:
            ValueError: D_S0 が S0 での値を定めていないフルエント記号があるとき
        """
        cases: list[tuple[Formula, Formula]] = []
        for sym in self.language.fluents.values():
            d = self.initial_definition_for(sym)
            if d is None:
                msg = f"D_S0 がフルエント {sym.name} の初期値を定めていない (完全でない)"
                raise ValueError(msg)
            cases.append((sym.recognize(p), d.instantiate(sym.arguments(p))))
        return _if_chain(cases)

    def one_step_instances(self, a: Action, s: Situation) -> tuple[Formula, ...]:
        """D_ss と D_ap の，状況 s と do(a, s) での具体例 (量化子なし)

        - 各基礎的なフルエント F(c⃗) について ``F(c⃗, do(a, s)) ≡ Φ_F(c⃗, a, s)``
        - ``Poss(a, s) ≡ Π(a, s)`` (行動の構成子での場合分け)

        いずれも D の公理から (全称例化とデータ型の領域閉包で) 従う．したがって
        これらから φ が帰結すれば D からも帰結する．s と do(a, s) だけに言及する性質
        (例: 状態制約が 1 ステップで保存されること) を，量化子なしで判定するのに使う
        構成子についての ∃ も消去しておく (同値な書き換え)

        Args:
            a: 行動の項 (通常は変数)
            s: 状況の項 (通常は変数)

        Returns:
            具体例のタプル
        """
        lang = self.language
        after = lang.do(a, s)
        instances = [
            lang.holds(f, after) == eliminate_constructor_quantifiers(self.holds_cases(f, a, s))
            for f in lang.ground_fluents()
        ]
        instances.append(
            lang.poss(a, s) == eliminate_constructor_quantifiers(self.poss_cases(a, s))
        )
        return tuple(instances)

    def compile(self) -> "CompiledTheory":
        """Holds, Poss, ⊏, Executable を再帰関数にコンパイルする (結果はキャッシュ)

        Returns:
            コンパイルした理論
        """
        if self._compiled is None:
            self._compiled = CompiledTheory(self)
        return self._compiled


def _params(sym: ActionSymbol | FluentSymbol, prefix: str) -> tuple[DomainObject, ...]:
    """関数記号の引数に対応する変数を作る

    Args:
        sym: 関数記号
        prefix: 変数名の接頭辞 (``x`` なら x1, x2, ...)

    Returns:
        変数のタプル
    """
    return tuple(p.var(f"{prefix}{i + 1}") for i, p in enumerate(sym.params))


def _if_chain(cases: Sequence[tuple[Formula, Formula]]) -> Formula:
    """``if c1 then φ1 else if c2 then φ2 ... else φn`` を作る

    最後の条件 cn は，データ型の領域閉包により省略する

    Args:
        cases: (条件, 式) の列

    Returns:
        場合分けの式 (cases が空なら偽)
    """
    if not cases:
        return z3.BoolVal(False)
    result = cases[-1][1]
    for cond, body in reversed(cases[:-1]):
        result = as_formula(z3.If(cond, body, result))
    return result


class CompiledTheory:
    """完全な D_S0 を持つ基本行動理論を，再帰関数で表したもの

    D_S0 が全フルエントの S0 での真偽を定めているとき，D_ss と合わせて Holds は
    状況の木の上で一意に決まる (状況についての帰納法 (16.63) による)．そこで

        Holds*(p, s) = if s = S0 then ψ(p)                 (D_S0)
                       else Φ(p, a', s')  where s = do(a', s')  (D_ss)

    という再帰関数 Holds* を定義すると，D のモデルの Holds と一致する
    Poss*, ⊏*, Executable* も同様．なお Executable* は「s から s' に到達できない」
    場合も偽と定める (公理版では未定義のまま)

    Attributes:
        theory: 元の基本行動理論
        holds_decl: 再帰関数 Holds*
        poss_decl: 再帰関数 Poss*
        precedes_decl: 再帰関数 ⊏*
        executable_decl: 再帰関数 Executable*
    """

    def __init__(self, theory: BasicActionTheory) -> None:
        """再帰関数を定義する

        Args:
            theory: 完全な D_S0 を持つ基本行動理論
        """
        self.theory = theory
        lang = theory.language
        b = lang.holds_decl.range()
        self.holds_decl: z3.FuncDeclRef = z3.RecFunction(
            f"Holds*_{lang.domain}", lang.fluent_sort, lang.situation_sort, b
        )
        self.poss_decl: z3.FuncDeclRef = z3.RecFunction(
            f"Poss*_{lang.domain}", lang.action_sort, lang.situation_sort, b
        )
        self.precedes_decl: z3.FuncDeclRef = z3.RecFunction(
            f"Precedes*_{lang.domain}", lang.situation_sort, lang.situation_sort, b
        )
        self.executable_decl: z3.FuncDeclRef = z3.RecFunction(
            f"Executable*_{lang.domain}", lang.situation_sort, lang.situation_sort, b
        )

        p = lang.fluent_var("p")
        a = lang.action_var("a")
        s, s2 = lang.situation_var("s"), lang.situation_var("s'")
        prev_a, prev_s = lang.do_action(s), lang.do_situation(s)

        holds_body = z3.If(
            lang.is_s0(s),
            theory.initial_cases(p),
            theory.holds_cases(p, prev_a, prev_s),
        )
        z3.RecAddDefinition(
            self.holds_decl, [p.expr, s.expr], self._prepare(as_formula(holds_body))
        )

        has_poss = all(theory.precondition_for(sym) is not None for sym in lang.actions.values())
        if has_poss:
            z3.RecAddDefinition(
                self.poss_decl, [a.expr, s.expr], self._prepare(theory.poss_cases(a, s))
            )

        prev2_a, prev2_s = lang.do_action(s2), lang.do_situation(s2)
        z3.RecAddDefinition(
            self.precedes_decl,
            [s.expr, s2.expr],
            z3.If(
                lang.is_do(s2), z3.Or(eq(s, prev2_s), self._precedes(s, prev2_s)), z3.BoolVal(False)
            ),
        )
        z3.RecAddDefinition(
            self.executable_decl,
            [s.expr, s2.expr],
            z3.If(
                eq(s, s2),
                z3.BoolVal(True),
                z3.If(
                    lang.is_do(s2),
                    z3.And(self._poss(prev2_a, prev2_s), self._executable(s, prev2_s)),
                    z3.BoolVal(False),
                ),
            ),
        )

    def _prepare(self, body: Formula) -> Formula:
        """再帰関数の本体: 再帰関数版に置き換え，構成子についての ∃ を消去する

        Args:
            body: 公理版の記号で書いた本体

        Returns:
            再帰関数の定義に使う本体
        """
        return eliminate_constructor_quantifiers(self.translate(body))

    def _app(self, f: z3.FuncDeclRef, *args: z3.ExprRef) -> Formula:
        """関数を適用した論理式を作る

        Args:
            f: Bool を返す関数
            *args: 引数

        Returns:
            論理式 ``f(args)``
        """
        return as_formula(f(*args))

    def _poss(self, a: Action, s: Situation) -> Formula:
        """``Poss*(a, s)`` を作る

        Args:
            a: 行動の項
            s: 状況の項

        Returns:
            論理式
        """
        return self._app(self.poss_decl, a.expr, s.expr)

    def _precedes(self, s: Situation, s2: Situation) -> Formula:
        """``s ⊏* s'`` を作る

        Args:
            s: 状況 s
            s2: 状況 s'

        Returns:
            論理式
        """
        return self._app(self.precedes_decl, s.expr, s2.expr)

    def _executable(self, s: Situation, s2: Situation) -> Formula:
        """``Executable*(s, s')`` を作る

        Args:
            s: 状況 s
            s2: 状況 s'

        Returns:
            論理式
        """
        return self._app(self.executable_decl, s.expr, s2.expr)

    def translate(self, phi: Formula) -> Formula:
        """φ 中の Holds, Poss, ⊏, Executable を再帰関数版に置き換える

        Args:
            phi: 公理版の記号 (Holds, Poss, ⊏, Executable) で書いた論理式

        Returns:
            再帰関数版の記号に置き換えた論理式
        """
        lang = self.theory.language
        f, sit, act = lang.fluent_sort, lang.situation_sort, lang.action_sort
        return as_formula(
            z3.substitute_funs(
                phi,
                (lang.holds_decl, self.holds_decl(z3.Var(0, f), z3.Var(1, sit))),
                (lang.poss_decl, self.poss_decl(z3.Var(0, act), z3.Var(1, sit))),
                (lang.precedes_decl, self.precedes_decl(z3.Var(0, sit), z3.Var(1, sit))),
                (lang.executable_decl, self.executable_decl(z3.Var(0, sit), z3.Var(1, sit))),
            )
        )

    def entails(self, phi: Formula, *, timeout_ms: int = DEFAULT_TIMEOUT_MS) -> Entailment:
        """再帰関数版で ``D ⊨ φ`` を判定する

        Args:
            phi: 論理式
            timeout_ms: Z3 の制限時間 (ミリ秒)

        Returns:
            判定結果
        """
        return entails([], self.translate(phi), timeout_ms=timeout_ms)

    def evaluator(self) -> "Evaluator":
        """基礎的な状況での真偽を計算する評価器を作る

        Returns:
            評価器
        """
        return Evaluator(self)


class Evaluator:
    """基礎的な状況項でのフルエント・Poss の真偽を，Z3 のモデル評価で計算する

    再帰関数はモデルの評価時に展開されるので，制約なしのソルバーのモデルで十分

    Attributes:
        compiled: コンパイルした理論
    """

    def __init__(self, compiled: CompiledTheory) -> None:
        """空のソルバーからモデルを得る

        Args:
            compiled: コンパイルした理論

        Raises:
            RuntimeError: 空の制約が充足不能だったとき (起こらないはず)
        """
        self.compiled = compiled
        solver = z3.Solver()
        if solver.check() != z3.sat:
            msg = "空の制約が充足不能 (起こらないはず)"
            raise RuntimeError(msg)
        self._model = solver.model()

    def truth(self, phi: Formula) -> bool:
        """基礎的な論理式の真偽を計算する

        Args:
            phi: 公理版の記号で書いた，基礎的な状況項についての論理式

        Returns:
            真なら True
        """
        return z3.is_true(self._model.eval(self.compiled.translate(phi), model_completion=True))

    def state(self, s: Situation) -> frozenset[Fluent]:
        """状況 s で真なフルエントの集合を計算する

        Args:
            s: 基礎的な状況項

        Returns:
            真な基礎的なフルエントの集合
        """
        lang = self.compiled.theory.language
        return frozenset(f for f in lang.ground_fluents() if self.truth(lang.holds(f, s)))

    def executable_actions(self, s: Situation) -> tuple[Action, ...]:
        """状況 s で実行可能な基礎的な行動を計算する

        Args:
            s: 基礎的な状況項

        Returns:
            Poss が真な基礎的な行動 (言語の宣言順)
        """
        lang = self.compiled.theory.language
        return tuple(a for a in lang.ground_actions() if self.truth(lang.poss(a, s)))
