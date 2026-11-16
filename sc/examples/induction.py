"""例 5: 帰納法と Z3 の限界 (§16.3, (16.63), p.664)

本書 p.664: 「基本行動理論で解ける問題の多くは一階の演繹で解けるが，∀s.C(s) の形の
一般的な性質の証明 (例: あるゴールが達成不能であること) には帰納法が要る」

Z3 は一階の自動証明器で，二階の帰納法公理 (16.63) を持たないし，帰納法を自動では使わない
そこで特定の性質 P について (16.63) の一階の具体例

    [P(S0) ∧ ∀a, s. P(s) ⊃ P(do(a, s))] ⊃ ∀s. P(s)

を作り，基底段階と帰納段階をそれぞれ Z3 で証明する

1. p.664 の例: D_ss = {loaded(do(a, s)) ≡ loaded(s)}, D_S0 = {loaded(S0)} で ∀s.loaded(s)
2. ブロック世界の状態制約 (p.657) が，S0 から実行可能なすべての状況で成り立つこと
"""

import z3

from sc.examples import blocks_world as bw
from sc.sitcalc.axioms import InitialAxiom, Sentence, SuccessorStateAxiom, forall
from sc.sitcalc.language import Formula, Signature, SitCalcLanguage, Situation
from sc.sitcalc.solving import Verdict, entails
from sc.sitcalc.theory import BasicActionTheory
from sc.viz.export import ExampleTrace
from sc.viz.terminal import Report

# ---------------------------------------------------------------------------
# 1. p.664 の例
# ---------------------------------------------------------------------------

LANG = SitCalcLanguage(
    "induction",
    # 本書は行動を特定していない．何でもよいので 2 つ置く
    actions=[Signature("noop"), Signature("look")],
    fluents=[Signature("loaded")],
)
loaded = LANG.fluents["loaded"]()
a = LANG.action_var("a")
s = LANG.situation_var("s")


def _loaded_theory() -> BasicActionTheory:
    """p.664 の基本行動理論を作る

    D_ap = ∅, D_ss = {loaded(do(a, s)) ≡ loaded(s)}, D_S0 = {loaded(S0)}

    Returns:
        基本行動理論
    """
    return BasicActionTheory(
        name="p.664 の例",
        language=LANG,
        d_ss=[
            SuccessorStateAxiom(
                language=LANG,
                fluent=LANG.fluents["loaded"],
                params=(),
                action=a,
                situation=s,
                phi=LANG.holds(loaded, s),
                ref="p.664",
            )
        ],
        d_ap=[],  # D_ap = ∅ (p.664)
        d_s0=[InitialAxiom(language=LANG, sentence=LANG.holds(loaded, LANG.s0), ref="p.664")],
    )


def run() -> ExampleTrace:
    """例題を実行する

    Returns:
        この例題の記録 (ビューア用．検査結果を含む)

    Raises:
        CheckFailedError: 期待と違う検査があったとき (記録は例外の ``trace`` に入る)
    """
    r = Report("induction", "例 5: 帰納法と Z3 の限界", "§16.3 (16.63), p.664")

    # 1 -----------------------------------------------------------------------
    r.section("1. p.664 の例: ∀s.loaded(s)", "p.664")
    bat = _loaded_theory()
    r.theory(bat)
    goal = forall([s], LANG.holds(loaded, s))
    r.formula("示したい性質", goal, "p.664")
    r.expect_entailment(
        "Z3 に直接聞く: D ⊨ ∀s.loaded(s)",
        bat.entails(goal, timeout_ms=10_000),
        Verdict.UNKNOWN,
        ref="p.664",
        detail="真だが、証明には帰納法が要る。Z3 は帰納法を自動では使わないので判定できない",
    )

    def prop(sit: Situation) -> Formula:
        """性質 P(s) := loaded(s)

        Args:
            sit: 状況の項

        Returns:
            論理式
        """
        return LANG.holds(loaded, sit)

    r.formula("(16.63) の P := loaded とした具体例", bat.induction_instance(prop), "(16.63)")
    r.expect_entailment(
        "基底段階: D ⊨ loaded(S0)", bat.entails(prop(LANG.s0)), Verdict.ENTAILED, ref="(16.63)"
    )
    r.expect_entailment(
        "帰納段階: D ⊨ ∀a, s. loaded(s) ⊃ loaded(do(a, s))",
        bat.entails(forall([a, s], z3.Implies(prop(s), prop(LANG.do(a, s))))),
        Verdict.ENTAILED,
        ref="(16.63)",
    )
    r.expect_entailment(
        "D ∪ {(16.63) の具体例} ⊨ ∀s.loaded(s)",
        entails([*bat.axioms(), bat.induction_instance(prop)], goal),
        Verdict.ENTAILED,
        ref="(16.63)",
    )

    # 2 -----------------------------------------------------------------------
    r.section("2. ブロック世界の状態制約は、実行可能なすべての状況で成り立つ", "p.657, (16.63)")
    blocks = bw.basic_action_theory("ブロック世界 (Sussman の異常)", bw.SUSSMAN_INITIAL)
    s0 = bw.LANG.s0
    ba = bw.LANG.action_var("a")
    bs = bw.LANG.situation_var("s")
    r.axiom_list(
        "状態制約 C(s)",
        "p.649–650, p.657",
        [
            Sentence(ref=ref, sentence=phi, display=text)
            for ref, text, phi in bw.state_constraints(bs)
        ],
    )

    def reachable_ok(sit: Situation) -> Formula:
        """P(s) := S0 ⊑ s ∧ (Executable(S0, s) ⊃ C(s))

        Args:
            sit: 状況の項

        Returns:
            論理式
        """
        return z3.And(
            bw.LANG.precedes_eq(s0, sit),
            z3.Implies(bw.LANG.executable(s0, sit), bw.constraints(sit)),
        )

    target = forall([bs], z3.Implies(bw.LANG.executable(s0, bs), bw.constraints(bs)))
    r.formula("示したい性質", target, "p.657")
    r.expect_entailment(
        "Z3 に直接聞く: D ⊨ ∀s. Executable(S0, s) ⊃ C(s)",
        blocks.entails(target, timeout_ms=10_000),
        Verdict.UNKNOWN,
        detail="これも帰納法が要る",
    )
    r.text(
        "帰納法の性質 P(s) は「S0 ⊑ s ∧ (Executable(S0, s) ⊃ C(s))」と少し強めておく"
        " (S0 ⊑ s がないと、帰納段階で Executable(S0, do(a, s)) を Poss(a, s) ∧ Executable(S0, s)"
        " に分解する (p.662 の定義, この実装では前提 S0 ⊏ do(a, s) 付き) ことができない)。"
    )
    r.formula("(16.63) の具体例", blocks.induction_instance(reachable_ok), "(16.63)")

    # 補題: C は実行可能な行動で保存される (制約ごとに示す)
    r.text(
        "補題: ∀a, s. C(s) ∧ Poss(a, s) ⊃ C(do(a, s))。"
        "この式は s と do(a, s) にしか言及しないので、"
        "D_ss と D_ap をその 2 点で具体化した量化子のない式 (D から従う) を前提にし、"
        "ブロックについての"
        "量化子は {A, B, C} 上の連言・選言に展開して解く (どちらも同値な書き換え)。"
    )
    one_step = blocks.one_step_instances(ba, bs)
    after = bw.LANG.do(ba, bs)
    premise = z3.And(bw.constraints(bs), bw.LANG.poss(ba, bs))
    rows: list[list[str]] = []
    all_ok = True
    for ref, text, phi in bw.state_constraints(after):
        res = entails(one_step, z3.Implies(premise, phi), expand_finite=True)
        all_ok = all_ok and res.entailed
        rows.append([ref, text, res.verdict.value])
    r.table(
        "C(s) ∧ Poss(a, s) ⊃ cᵢ(do(a, s))",
        ["出典", "制約 cᵢ(s) (これの s を do(a, s) にしたものを示す)", "結果"],
        rows,
    )
    r.expect(
        "補題: すべての制約が 1 ステップで保存される",
        ok=all_ok,
        actual="すべて帰結する" if all_ok else "帰結しない制約がある",
        expected="すべて帰結する",
        ref="p.657",
        detail=(
            "最初は「片手」と「持っているブロックの上には何もない」の 2 つの制約を入れておらず、"
            "Z3 が反例 (A を持ったまま C が A の上にある状態で putdown(A) など) を返した"
        ),
    )
    lemma = forall([ba, bs], z3.Implies(premise, bw.constraints(after)))

    r.expect_entailment(
        "基底段階: D ⊨ P(S0)",
        blocks.entails(reachable_ok(s0), expand_finite=True),
        Verdict.ENTAILED,
        ref="(16.63)",
    )
    step_premises = [
        lemma,
        *(ax.formula for ax in blocks.sigma().axioms),
        *(ax.formula for ax in blocks.definitions().axioms),
    ]
    r.expect_entailment(
        "帰納段階: 補題 ∪ Σ ∪ Executable の定義 ⊨ ∀a, s. P(s) ⊃ P(do(a, s))",
        entails(
            step_premises,
            forall([ba, bs], z3.Implies(reachable_ok(bs), reachable_ok(bw.LANG.do(ba, bs)))),
            expand_finite=True,
        ),
        Verdict.ENTAILED,
        ref="(16.63)",
        detail=(
            "(16.65) で S0 ⊑ s から S0 ⊏ do(a, s)、"
            "修正した Executable の定義で Poss(a, s) ∧ Executable(S0, s) に分解"
        ),
    )
    r.expect_entailment(
        "(16.63) の具体例 ∪ P(S0) ∪ 帰納段階 ⊨ ∀s. Executable(S0, s) ⊃ C(s)",
        entails(
            [
                blocks.induction_instance(reachable_ok),
                reachable_ok(s0),
                forall([ba, bs], z3.Implies(reachable_ok(bs), reachable_ok(bw.LANG.do(ba, bs)))),
            ],
            target,
        ),
        Verdict.ENTAILED,
        ref="(16.63)",
    )
    return r.finish()


def main() -> None:
    """コマンドラインから実行する"""
    run()


if __name__ == "__main__":
    main()
