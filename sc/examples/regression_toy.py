"""例 0: 回帰の定義の小さな例 (§16.3, p.664–665)

本書 p.665 の例: 後継状態公理

    F(do(a, s)) ≡ a = A ∨ F(s),
    G(do(a, s)) ≡ (a = B ∧ F(s)) ∨ G(s)

のもとで，G(do(B, do(A, S0))) の回帰は

    (B = B ∧ (A = A ∨ F(S0))) ∨ (A = B ∧ F(S0)) ∨ G(S0)

となり，これは true と同値．したがって D_S0 が空でも D ⊨ G(do(B, do(A, S0)))
"""

import z3

from sc.sitcalc.axioms import SuccessorStateAxiom
from sc.sitcalc.language import Signature, SitCalcLanguage, eq
from sc.sitcalc.pretty import show
from sc.sitcalc.regression import entailed_by_initial_database, regress
from sc.sitcalc.solving import Verdict
from sc.sitcalc.theory import BasicActionTheory
from sc.viz.export import ExampleTrace
from sc.viz.terminal import Report

LANG = SitCalcLanguage(
    "regression",
    actions=[Signature("A"), Signature("B")],
    fluents=[Signature("F"), Signature("G")],
)
A = LANG.actions["A"]()
B = LANG.actions["B"]()
F = LANG.fluents["F"]()
G = LANG.fluents["G"]()
a = LANG.action_var("a")
s = LANG.situation_var("s")
holds = LANG.holds
do = LANG.do
S0 = LANG.s0

BAT = BasicActionTheory(
    name="p.665 の回帰の例",
    language=LANG,
    d_ss=[
        # F(do(a, s)) ≡ a = A ∨ F(s)
        SuccessorStateAxiom(
            language=LANG,
            fluent=LANG.fluents["F"],
            params=(),
            action=a,
            situation=s,
            phi=z3.Or(eq(a, A), holds(F, s)),
            ref="p.665",
        ),
        # G(do(a, s)) ≡ (a = B ∧ F(s)) ∨ G(s)
        SuccessorStateAxiom(
            language=LANG,
            fluent=LANG.fluents["G"],
            params=(),
            action=a,
            situation=s,
            phi=z3.Or(z3.And(eq(a, B), holds(F, s)), holds(G, s)),
            ref="p.665",
        ),
    ],
    d_ap=[],  # この例では Poss を使わない
    d_s0=[],  # D_S0 は空 (S0 について何も知らない)
)


# 画面に出す説明文
SIMPLIFY_NOTE = (
    "本書は 1 段目を (B = B ∧ F(do(A, S0))) ∨ G(do(A, S0)) と書くが、"
    "この実装は各段で Z3 の simplify をかけるので、B = B のような自明な部分は消えている。"
)
NO_COUNTERMODEL_NOTE = (
    "「従わない」ことを示すには反例モデルが要るが、量化子を含む D のモデルを Z3 は作れない"
)
COUNTERMODEL_NOTE = (
    "回帰の結果は S0 についての量化子のない式なので、Z3 が反例 (F(S0) = G(S0) = 偽) を見つけられる"
)


def run() -> ExampleTrace:
    """例題を実行する

    Returns:
        この例題の記録 (ビューア用．検査結果を含む)

    Raises:
        CheckFailedError: 期待と違う検査があったとき (記録は例外の ``trace`` に入る)
    """
    r = Report("regression_toy", "例 0: 回帰の小さな例", "§16.3 (p.664–665)")

    r.section("基本行動理論", "p.665")
    r.theory(BAT)

    _regress_book_example(r)
    _compare_reversed_order(r)

    return r.finish()


def _regress_book_example(r: Report) -> None:
    """本書 p.665 の例: G(do(B, do(A, S0))) を回帰する

    Args:
        r: 出力先のレポート
    """
    r.section("1. G(do(B, do(A, S0))) の回帰", "p.664–665")

    # 回帰する式
    goal = holds(G, do(B, do(A, S0)))
    r.formula("回帰する式", goal, "p.665")

    # 1 段ずつ回帰して，各段の式を表示する
    reg = regress(BAT, goal)
    for i, step in enumerate(reg.steps, start=1):
        r.formula(f"{i} 段目 (simplify 後)", step, "p.665")
    r.text(SIMPLIFY_NOTE)

    # 回帰の結果は true になる (p.665 「which is equivalent to true」)
    result_text = show(reg.result)
    r.expect(
        "回帰の結果は true",
        ok=result_text == "true",
        actual=result_text,
        expected="true",
        ref="p.665",
    )

    # 回帰の結果が D_una ∪ D_S0 から従うので，元の式は D から従う (p.664)
    by_regression = entailed_by_initial_database(BAT, reg.result)
    r.expect_entailment(
        "D_una ∪ D_S0 ⊨ 回帰の結果 (D_S0 は空)",
        by_regression,
        Verdict.ENTAILED,
        ref="p.664",
    )

    # 回帰せずに D に直接聞いても，帰結すると判定できる
    direct = BAT.entails(goal)
    r.expect_entailment(
        "直接: D ⊨ G(do(B, do(A, S0)))",
        direct,
        Verdict.ENTAILED,
        ref="p.665",
    )


def _compare_reversed_order(r: Report) -> None:
    """比較: 行動の順序を逆にした G(do(A, do(B, S0))) は D から従わない

    「従わない」ことは，D に直接聞くと Z3 には判定できないが，回帰すれば判定できる

    Args:
        r: 出力先のレポート
    """
    r.section("2. 比較: 行動の順序を逆にする", "p.664–665")

    goal = holds(G, do(A, do(B, S0)))
    r.formula("調べる式", goal, "p.665")

    # D に直接聞く: 反例モデルが要るが，量化子を含む D のモデルを Z3 は作れない
    direct = BAT.entails(goal, timeout_ms=5_000)
    r.expect_entailment(
        "直接: D ⊨ G(do(A, do(B, S0))) ?",
        direct,
        Verdict.UNKNOWN,
        ref="p.665",
        detail=NO_COUNTERMODEL_NOTE,
    )

    # 回帰する: 結果は S0 についての量化子のない式になる
    reg = regress(BAT, goal)
    r.formula("回帰の結果", reg.result, "p.665")

    # 量化子のない式なので，Z3 は反例 (F(S0) = G(S0) = 偽) を見つけられる
    by_regression = entailed_by_initial_database(BAT, reg.result)
    r.expect_entailment(
        "回帰: D_una ∪ D_S0 ⊨ 回帰の結果 ?",
        by_regression,
        Verdict.NOT_ENTAILED,
        ref="p.664",
        detail=COUNTERMODEL_NOTE,
    )


def main() -> None:
    """コマンドラインから実行する"""
    run()


if __name__ == "__main__":
    main()
