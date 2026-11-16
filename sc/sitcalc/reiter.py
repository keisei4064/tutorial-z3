"""フレーム問題に対する Reiter の解 (§16.2.1, p.654–656)

効果公理 (effect axiom) の集まりから後継状態公理 (16.50) を機械的に作る

1. 各効果公理を次のどちらかの形に書き換える (p.655):

       γ(a, x⃗, s) ⊃ F(x⃗, do(a, s))
       γ(a, x⃗, s) ⊃ ¬F(x⃗, do(a, s))

   例: (16.34) ¬clear(y, do(stack(x, y), s)) は (∃y) a = stack(y, x) ⊃ ¬clear(x, do(a, s))
   (本書 p.655．この実装ではフルエントの引数を u⃗ と書く)

2. フルエント F について，正の γ を γ⁺₁ ... γ⁺ₘ，負の γ を γ⁻₁ ... γ⁻ₙ とし
   因果的完全性の仮定 (causal completeness assumption) のもとで (16.50):

       F(x⃗, do(a, s)) ≡ γ⁺(a, x⃗, s) ∨ (F(x⃗, s) ∧ ¬γ⁻(a, x⃗, s))

   ただし γ⁺ = γ⁺₁ ∨ ... ∨ γ⁺ₘ, γ⁻ = γ⁻₁ ∨ ... ∨ γ⁻ₙ

3. 整合性の仮定 (consistency assumption, p.656): 背景理論から ¬(γ⁺ ∧ γ⁻) が従うこと
"""

from collections.abc import Sequence
from dataclasses import dataclass

import z3

from sc.sitcalc.axioms import Axiom, SuccessorStateAxiom, forall, instantiate
from sc.sitcalc.language import (
    Action,
    DomainObject,
    Fluent,
    FluentSymbol,
    Formula,
    SitCalcLanguage,
    Situation,
    Term,
    as_datatype_term,
    eq,
    is_variable,
)
from sc.sitcalc.pretty import show


@dataclass(frozen=True, eq=False, kw_only=True)
class EffectAxiom(Axiom):
    """効果公理 (effect axiom): ``φ(x⃗, s) ⊃ (¬)F(t⃗, do(A(r⃗), s))``

    本書 (16.32)–(16.49) は条件 φ のない形 (φ = true)．条件付きの例は (16.30)

    Attributes:
        language: 言語
        positive: F を真にする (True) か偽にする (False) か
        fluent: フルエントの項 F(t⃗) (変数を含んでよい)
        action: 行動の項 A(r⃗) (変数を含んでよい)
        situation: 状況の変数 s
        variables: s 以外の自由変数 x⃗ (すべて列挙する)
        condition: 条件 φ(x⃗, s) (s で uniform)．None なら true

    """

    language: SitCalcLanguage
    positive: bool
    fluent: Fluent
    action: Action
    situation: Situation
    variables: tuple[DomainObject, ...] = ()
    condition: Formula | None = None

    @property
    def _condition(self) -> Formula:
        """条件 φ を返す (None なら true)

        Returns:
            条件の論理式
        """
        return z3.BoolVal(True) if self.condition is None else self.condition

    @property
    def consequent(self) -> Formula:
        """``(¬)F(t⃗, do(A(r⃗), s))``"""
        lang = self.language
        atom = lang.holds(self.fluent, lang.do(self.action, self.situation))
        return atom if self.positive else z3.Not(atom)

    @property
    def formula(self) -> Formula:
        """``∀x⃗, s. φ ⊃ (¬)F(t⃗, do(A(r⃗), s))``"""
        body = (
            self.consequent
            if self.condition is None
            else z3.Implies(self._condition, self.consequent)
        )
        return forall([*self.variables, self.situation], body)

    def statement(self) -> str:
        """本書の書き方で表示する

        Returns:
            表示用の文字列
        """
        if self.condition is None:
            return show(self.consequent)
        return f"{show(self._condition)} ⊃ {show(self.consequent)}"

    def normal_form(self, params: Sequence[DomainObject], a: Action, s: Situation) -> Formula:
        """γ(a, u⃗, s): この効果公理を ``γ(a, u⃗, s) ⊃ (¬)F(u⃗, do(a, s))`` の形にしたときの γ

        F(t⃗) の引数 t_i が (まだ使っていない) 変数なら u_i に名前を付け替え
        そうでなければ等式 u_i = t_i を加える．残った変数は存在量化する

        Args:
            params: SSA の変数 u⃗ (F の引数)
            a: SSA の変数 a
            s: SSA の変数 s

        Returns:
            γ(a, u⃗, s)

        Raises:
            ValueError: u⃗ の個数が F の引数と合わない，または効果公理の変数と名前が衝突するとき
        """
        sym = self.language.fluent_symbol_of(self.fluent)
        args = [DomainObject(as_datatype_term(c)) for c in self.fluent.expr.children()]
        if len(params) != sym.arity:
            msg = f"{sym.name} の引数は {sym.arity} 個"
            raise ValueError(msg)
        clash = {v.expr.hash() for v in self.variables} & {u.expr.hash() for u in params}
        if clash:
            msg = "効果公理の変数と SSA の変数 u⃗ の名前が衝突している"
            raise ValueError(msg)

        renamed: list[Term] = []
        renamed_to: list[Term] = []
        equalities: list[tuple[DomainObject, DomainObject]] = []
        own = {v.expr.hash() for v in self.variables}
        for t, u in zip(args, params, strict=True):
            if (
                is_variable(t)
                and t.expr.hash() in own
                and not any(t.expr.eq(r.expr) for r in renamed)
            ):
                renamed.append(t)
                renamed_to.append(u)
            else:
                equalities.append((u, t))

        def rename(phi: Formula) -> Formula:
            """効果公理側の変数を u⃗ と s に付け替える

            Args:
                phi: 効果公理側の論理式

            Returns:
                付け替えた論理式
            """
            return instantiate(phi, [*renamed, self.situation], [*renamed_to, s])

        body = [rename(eq(a, self.action))]
        body += [rename(eq(u, t)) for u, t in equalities]
        if self.condition is not None:
            body.append(rename(self.condition))
        gamma = z3.And(*body) if len(body) > 1 else body[0]
        rest = [v for v in self.variables if not any(v.expr.eq(r.expr) for r in renamed)]
        if rest:
            gamma = z3.Exists([v.expr for v in rest], gamma)
        return gamma


@dataclass(frozen=True, eq=False)
class ReiterDerivation:
    """Reiter の手続きの途中経過 (表示用) と結果の後継状態公理

    Attributes:
        fluent: フルエント記号 F
        positive: F を真にする効果公理と，その γ の組
        negative: F を偽にする効果公理と，その γ の組
        gamma_plus: γ⁺ = γ⁺₁ ∨ ... ∨ γ⁺ₘ
        gamma_minus: γ⁻ = γ⁻₁ ∨ ... ∨ γ⁻ₙ
        ssa: 結果の後継状態公理 (16.50)
        consistency: 整合性の仮定 ``∀u⃗, a, s. ¬(γ⁺ ∧ γ⁻)`` (p.656)
    """

    fluent: FluentSymbol
    positive: tuple[tuple[EffectAxiom, Formula], ...]
    negative: tuple[tuple[EffectAxiom, Formula], ...]
    gamma_plus: Formula
    gamma_minus: Formula
    ssa: SuccessorStateAxiom
    consistency: Formula


def successor_state_axiom(
    language: SitCalcLanguage,
    fluent: FluentSymbol,
    effects: Sequence[EffectAxiom],
    *,
    params: Sequence[DomainObject],
    action: Action,
    situation: Situation,
    ref: str = "(16.50)",
    note: str = "",
) -> ReiterDerivation:
    """効果公理から F の後継状態公理 (16.50) を作る

    Args:
        language: 言語
        fluent: フルエント記号 F
        effects: 効果公理 (F 以外のものは無視する)
        params: SSA の変数 u⃗ (F の引数)
        action: SSA の変数 a
        situation: SSA の変数 s
        ref: 出典
        note: 補足

    Returns:
        途中経過 (γ⁺, γ⁻) と，結果の後継状態公理
    """
    mine = [e for e in effects if fluent.matches(e.fluent)]
    pos = tuple((e, e.normal_form(params, action, situation)) for e in mine if e.positive)
    neg = tuple((e, e.normal_form(params, action, situation)) for e in mine if not e.positive)
    gamma_plus = _disjunction([g for _, g in pos])
    gamma_minus = _disjunction([g for _, g in neg])
    now = language.holds(fluent(*params), situation)
    if neg:
        phi = (
            z3.Or(gamma_plus, z3.And(now, z3.Not(gamma_minus)))
            if pos
            else z3.And(now, z3.Not(gamma_minus))
        )
    else:
        phi = z3.Or(gamma_plus, now) if pos else now
    ssa = SuccessorStateAxiom(
        language=language,
        fluent=fluent,
        params=tuple(params),
        action=action,
        situation=situation,
        phi=phi,
        ref=ref,
        note=note,
    )
    consistency = forall([*params, action, situation], z3.Not(z3.And(gamma_plus, gamma_minus)))
    return ReiterDerivation(fluent, pos, neg, gamma_plus, gamma_minus, ssa, consistency)


def _disjunction(fs: Sequence[Formula]) -> Formula:
    """選言を作る

    Args:
        fs: 論理式

    Returns:
        ``fs[0] ∨ ... ∨ fs[n-1]`` (空なら偽，1 つならそれ自身)
    """
    if not fs:
        return z3.BoolVal(False)
    return fs[0] if len(fs) == 1 else z3.Or(*fs)
