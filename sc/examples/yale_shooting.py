"""例 1: Yale Shooting Problem とフレーム問題 (§16.2, p.652–656).

本書の流れに沿って、次を Z3 で確かめる:

1. 効果公理 (16.29)–(16.30) と初期状態 (16.31) だけでは、
   dead(do(shoot, do(wait, do(load, S0)))) は一階論理で帰結しない (フレーム問題)。
2. McCarthy の一般フレーム公理 (16.28) + abnormal のサーカムスクリプション (p.653–654)。
   ※ 本書の (16.28) は「真の持続」しか述べず、効果公理 (16.29)–(16.30) も abnormal に
   触れない。この組み合わせでは abnormal が空のモデルが唯一の極小モデルで、異常は
   起きない。Hanks と McDermott の定式化 (McCarthy 1986 に従い、効果公理が
   「その変化は abnormal」とも述べる) にすると、極小な abnormal の集合が 2 つになり、
   wait で弾が抜けるモデルが現れる。両方を Z3 で確かめる。
3. 効果の完全な仕様 (p.654 の 6 つの公理) からは帰結する。
4. Reiter の手続き (16.50) で効果公理から後継状態公理を作ると、
   p.654 の完全な仕様と同値な基本行動理論が得られる。
"""

from collections.abc import Callable

from z3 import And, BoolSort, BoolVal, Function, Implies, Not, Or, is_true

from sc.sitcalc.axioms import (
    ActionPreconditionAxiom,
    Axiom,
    InitialAxiom,
    Sentence,
    forall,
)
from sc.sitcalc.language import (
    Action,
    Fluent,
    Formula,
    Signature,
    SitCalcLanguage,
    Situation,
    as_formula,
)
from sc.sitcalc.minimal import minimal_models
from sc.sitcalc.pretty import show
from sc.sitcalc.regression import entailed_by_initial_database, regress
from sc.sitcalc.reiter import EffectAxiom, successor_state_axiom
from sc.sitcalc.solving import Satisfiability, Verdict, entails, satisfiable
from sc.sitcalc.theory import BasicActionTheory
from sc.viz.export import ExampleTrace
from sc.viz.terminal import Report

# ---------------------------------------------------------------------------
# 言語 (p.653): 行動 wait (何もしない), load (銃に弾を込める), shoot (撃つ)
# ---------------------------------------------------------------------------

LANG = SitCalcLanguage(
    "ysp",
    actions=[Signature("load"), Signature("wait"), Signature("shoot")],
    fluents=[Signature("loaded"), Signature("dead")],
)
load: Action = LANG.actions["load"]()
wait: Action = LANG.actions["wait"]()
shoot: Action = LANG.actions["shoot"]()
loaded: Fluent = LANG.fluents["loaded"]()
dead: Fluent = LANG.fluents["dead"]()

do = LANG.do
holds = LANG.holds
S0 = LANG.s0
a = LANG.action_var("a")
s = LANG.situation_var("s")

# 物語に出てくる状況
S1 = do(load, S0)
S2 = do(wait, S1)
S3 = do(shoot, S2)
NARRATIVE: tuple[tuple[str, Situation], ...] = (
    ("S0", S0),
    ("S1 = do(load, S0)", S1),
    ("S2 = do(wait, S1)", S2),
    ("S3 = do(shoot, S2)", S3),
)

# 問い: dead(do(shoot, do(wait, do(load, S0))))
GOAL: Formula = holds(dead, S3)

# ---------------------------------------------------------------------------
# 効果公理 (16.29), (16.30) と初期状態 (16.31)
# ---------------------------------------------------------------------------

EFFECT_AXIOMS: tuple[EffectAxiom, ...] = (
    # (16.29) loaded(do(load, s))
    EffectAxiom(
        language=LANG, positive=True, fluent=loaded, action=load, situation=s, ref="(16.29)"
    ),
    # (16.30) loaded(s) ⊃ dead(do(shoot, s))
    EffectAxiom(
        language=LANG,
        positive=True,
        fluent=dead,
        action=shoot,
        situation=s,
        condition=holds(loaded, s),
        ref="(16.30)",
    ),
)

# (16.31) ¬loaded(S0) ∧ ¬dead(S0)
INITIAL = InitialAxiom(
    language=LANG, sentence=And(Not(holds(loaded, S0)), Not(holds(dead, S0))), ref="(16.31)"
)

# 本書は Poss を与えていない。どの行動も常に実行可能とする
PRECONDITIONS: tuple[ActionPreconditionAxiom, ...] = tuple(
    ActionPreconditionAxiom(
        language=LANG,
        action_symbol=sym,
        params=(),
        situation=s,
        pi=BoolVal(True),
        ref="—",
        note="本書には前提条件の記述がないので、常に実行可能とした",
    )
    for sym in LANG.actions.values()
)

# ---------------------------------------------------------------------------
# p.654: 効果の完全な仕様 (6 つの公理)
# ---------------------------------------------------------------------------


def _complete_specification() -> tuple[Axiom, ...]:
    """p.654 の効果の完全な仕様 (6 つの公理) を作る.

    Returns:
        6 つの文 (s について全称閉包)。
    """

    def ax(phi: Formula, display: str) -> Sentence:
        """s について全称閉包した文を作る.

        Args:
            phi: s を自由変数に持つ論理式。
            display: 表示用の文字列。

        Returns:
            文。
        """
        return Sentence(ref="p.654", sentence=forall([s], phi), display=display)

    return (
        ax(holds(loaded, do(load, s)), "loaded(do(load, s))"),
        ax(holds(dead, do(load, s)) == holds(dead, s), "dead(do(load, s)) ≡ dead(s)"),
        ax(holds(loaded, do(shoot, s)) == holds(loaded, s), "loaded(do(shoot, s)) ≡ loaded(s)"),
        ax(
            holds(dead, do(shoot, s)) == Or(holds(loaded, s), holds(dead, s)),
            "dead(do(shoot, s)) ≡ loaded(s) ∨ dead(s)",
        ),
        ax(holds(loaded, do(wait, s)) == holds(loaded, s), "loaded(do(wait, s)) ≡ loaded(s)"),
        ax(holds(dead, do(wait, s)) == holds(dead, s), "dead(do(wait, s)) ≡ dead(s)"),
    )


COMPLETE_SPECIFICATION = _complete_specification()

# ---------------------------------------------------------------------------
# (16.28) McCarthy の一般フレーム公理 (abnormal 付き)
# ---------------------------------------------------------------------------

abnormal = Function("abnormal", LANG.fluent_sort, LANG.action_sort, LANG.situation_sort, BoolSort())


def ab(p: Fluent, act: Action, sit: Situation) -> Formula:
    """``abnormal(p, a, s)`` を作る.

    Args:
        p: フルエントの項。
        act: 行動の項。
        sit: 状況の項。

    Returns:
        論理式。
    """
    return as_formula(abnormal(p.expr, act.expr, sit.expr))


def frame_axiom(p: Fluent, act: Action, sit: Situation) -> Formula:
    """(16.28): ``Holds(p, s) ∧ ¬abnormal(p, a, s) ⊃ Holds(p, do(a, s))``.

    (本書の式は ⊃ が脱落している)

    Args:
        p: フルエントの項。
        act: 行動の項。
        sit: 状況の項。

    Returns:
        論理式 (基礎例)。
    """
    return Implies(And(holds(p, sit), Not(ab(p, act, sit))), holds(p, do(act, sit)))


def _circumscription_premises(
    *, effects_abnormal: bool
) -> tuple[list[Formula], list[Formula], list[str]]:
    """物語の遷移 S0 -load→ S1 -wait→ S2 -shoot→ S3 に制限した基礎例と、最小化する原子.

    Hanks–McDermott の議論 (p.654) は物語の上でのもの。物語の外の遷移まで含めると、
    そこでの abnormal も最小化の対象になり、関係のない極小モデルが増える。

    Args:
        effects_abnormal: 効果公理が「その変化は abnormal」とも述べるか
            (ab(loaded, load, s) と loaded(s) ⊃ ab(dead, shoot, s))。

    Returns:
        (前提, 最小化する abnormal の原子, 原子の表示名) の組。
    """
    premises: list[Formula] = [INITIAL.formula]
    atoms: list[Formula] = []
    names: list[str] = []
    for act, i in ((load, 0), (wait, 1), (shoot, 2)):
        sit_name, sit = NARRATIVE[i]
        premises.append(holds(loaded, do(load, sit)))  # (16.29)
        premises.append(Implies(holds(loaded, sit), holds(dead, do(shoot, sit))))  # (16.30)
        if effects_abnormal:
            premises.append(ab(loaded, load, sit))
            premises.append(Implies(holds(loaded, sit), ab(dead, shoot, sit)))
        for p in (loaded, dead):
            premises.append(frame_axiom(p, act, sit))
            atoms.append(ab(p, act, sit))
            names.append(f"ab({p}, {act}, {sit_name.split(' ')[0]})")
    return premises, atoms, names


def _possible_values(
    premises: list[Formula], atoms: list[Formula], true: tuple[int, ...], phi: Formula
) -> str:
    """abnormal の外延がちょうど true であるモデルで、φ が取りうる値を調べる.

    Args:
        premises: 前提。
        atoms: abnormal の原子。
        true: 真にする原子の添字 (それ以外は偽)。
        phi: 調べる論理式。

    Returns:
        ``"T"``、``"F"``、``"T/F"`` (両方取りうる) のいずれか。
    """
    exact = [atoms[i] if i in true else Not(atoms[i]) for i in range(len(atoms))]
    values = [
        label
        for label, q in (("T", phi), ("F", Not(phi)))
        if satisfiable([*premises, *exact, q]).status is Satisfiability.SAT
    ]
    return "/".join(values)


# ---------------------------------------------------------------------------
# 実行
# ---------------------------------------------------------------------------


def _narrative_values(truth: Callable[[Formula], bool]) -> list[str]:
    """物語の各状況での loaded と dead の値を、表のセルにする.

    Args:
        truth: 論理式の真偽を返す関数 (モデルの評価など)。

    Returns:
        状況ごとの ``loaded=T dead=F`` のような文字列。
    """
    cells: list[str] = []
    for _, sit in NARRATIVE:
        lv = "T" if truth(holds(loaded, sit)) else "F"
        dv = "T" if truth(holds(dead, sit)) else "F"
        cells.append(f"loaded={lv} dead={dv}")
    return cells


def run() -> ExampleTrace:
    """例題を実行する.

    Returns:
        この例題の記録 (ビューア用。検査結果を含む)。

    Raises:
        CheckFailedError: 期待と違う検査があったとき (記録は例外の ``trace`` に入る)。
    """
    r = Report("yale_shooting", "例 1: Yale Shooting Problem とフレーム問題", "§16.2 (p.652–656)")

    # 1. 効果公理だけ ---------------------------------------------------------
    r.section("1. 効果公理だけでは帰結しない (フレーム問題)", "(16.29)–(16.31)")
    r.axiom_list("効果公理と初期状態", "(16.29)–(16.31)", [*EFFECT_AXIOMS, INITIAL])
    r.formula("問い", GOAL)
    effect_only = entails([e.formula for e in EFFECT_AXIOMS] + [INITIAL.formula], GOAL)
    r.expect_entailment(
        "効果公理だけから dead(do(shoot, do(wait, do(load, S0)))) が従うか",
        effect_only,
        Verdict.NOT_ENTAILED,
        ref="p.653",
        detail=(
            "効果公理は「変わるもの」しか述べず、"
            "「変わらないもの」(wait で loaded が保たれる等) を述べていない"
        ),
    )
    if effect_only.countermodel is not None:
        m = effect_only.countermodel

        def truth_m(phi: Formula) -> bool:
            """反例モデルでの論理式の真偽.

            Args:
                phi: 論理式。

            Returns:
                真なら True。
            """
            return is_true(m.eval(phi, model_completion=True))

        r.table(
            "反例モデル (物語の各状況でのフルエントの値)",
            [n for n, _ in NARRATIVE],
            [_narrative_values(truth_m)],
        )

    # 2. (16.28) + サーカムスクリプション ---------------------------------------
    r.section("2. 一般フレーム公理 (16.28) と abnormal の最小化", "(16.28), p.653–654")
    r.text(
        "(16.28) の abnormal をサーカムスクリプションで最小化する (Holds は可変)。Z3 では二階の"
        "サーカムスクリプションを直接扱えないので、Hanks–McDermott と同じく物語の遷移"
        " S0 -load→ S1 -wait→ S2 -shoot→ S3 での基礎例に制限し、abnormal の原子の集合が"
        "包含について極小なモデルを列挙する。"
    )
    loaded_s2 = holds(loaded, S2)
    for effects_abnormal, label, n_expected in (
        (False, "(a) 本書どおり: (16.28) + (16.29)–(16.31)", 1),
        (True, "(b) Hanks–McDermott: 効果公理が「その変化は abnormal」とも述べる", 2),
    ):
        premises, atoms, names = _circumscription_premises(effects_abnormal=effects_abnormal)
        models = sorted(
            minimal_models(premises, atoms), key=lambda mm: [names[j] for j in mm.true_atoms]
        )
        rows = [
            [
                f"#{i + 1}",
                ", ".join(names[j] for j in mm.true_atoms) or "(なし)",
                _possible_values(premises, atoms, mm.true_atoms, loaded_s2),
                _possible_values(premises, atoms, mm.true_atoms, GOAL),
            ]
            for i, mm in enumerate(models)
        ]
        r.table(
            f"極小な abnormal の集合 — {label}",
            ["", "abnormal (真の原子)", "loaded(S2)", "dead(S3)"],
            rows,
        )
        refuting = [row for row in rows if "F" in row[3].split("/")]
        r.expect(
            f"{label[:3]} 極小な abnormal の集合の個数",
            ok=len(models) == n_expected,
            actual=f"{len(models)} 個",
            expected=f"{n_expected} 個",
            ref="p.654",
        )
        r.expect(
            f"{label[:3]} サーカムスクリプションから dead(S3) が帰結するか",
            ok=(not refuting) == (not effects_abnormal),
            actual="帰結する (どの極小モデルでも dead(S3))"
            if not refuting
            else "帰結しない (¬dead(S3) の極小モデルがある)",
            expected="帰結する" if not effects_abnormal else "帰結しない",
            ref="p.654",
            detail=(
                "(16.28) は真の持続しか述べないので、dead が F→T に変わるのに abnormal は要らない。"
                "abnormal が空のモデル (loaded が保たれ shoot で dead) が唯一の極小モデル"
                if not effects_abnormal
                else "ab(loaded, wait, S1) を含む方が Hanks–McDermott の直観に反するモデル: "
                "wait が abnormal に弾を抜き (loaded(S2) = F)、"
                "shoot の効果 ab(dead, shoot, S2) を避けている"
            ),
        )

    # 3. 完全な仕様 ------------------------------------------------------------
    r.section("3. 効果の完全な仕様からは帰結する", "p.654")
    r.axiom_list("効果の完全な仕様", "p.654", COMPLETE_SPECIFICATION)
    complete = entails([ax.formula for ax in COMPLETE_SPECIFICATION] + [INITIAL.formula], GOAL)
    r.expect_entailment(
        "完全な仕様 + (16.31) ⊨ dead(do(shoot, do(wait, do(load, S0))))",
        complete,
        Verdict.ENTAILED,
        ref="p.654",
    )

    # 4. Reiter の手続き → 基本行動理論 -------------------------------------------
    r.section("4. Reiter の手続きで後継状態公理を作る", "§16.2.1 (16.50)")
    derivations = [
        successor_state_axiom(
            LANG, sym, EFFECT_AXIOMS, params=(), action=a, situation=s, ref="(16.50)"
        )
        for sym in LANG.fluents.values()
    ]
    for d in derivations:
        r.formula(f"{d.fluent.name}: γ⁺", d.gamma_plus, "p.655")
        r.formula(f"{d.fluent.name}: γ⁻", d.gamma_minus, "p.655")
        r.formula(f"{d.fluent.name}: 後継状態公理", d.ssa.statement(), "(16.50)")
        r.expect_entailment(
            f"{d.fluent.name}: 整合性の仮定 ¬(γ⁺ ∧ γ⁻)",
            entails([], d.consistency),
            Verdict.ENTAILED,
            ref="p.656",
        )

    bat = BasicActionTheory(
        name="Yale Shooting",
        language=LANG,
        d_ss=[d.ssa for d in derivations],
        d_ap=PRECONDITIONS,
        d_s0=[INITIAL],
    )
    r.theory(bat)
    r.expect_sat(
        "定理 16.1: D_una ∪ D_S0 は充足可能 (よって D も充足可能)",
        bat.relative_satisfiability(),
        Satisfiability.SAT,
        ref="Theorem 16.1",
    )
    for ax in COMPLETE_SPECIFICATION:
        r.expect_entailment(
            f"D ⊨ {ax.statement()}", bat.entails(ax.formula), Verdict.ENTAILED, ref="p.654"
        )
    spec_and_una = [ax.formula for ax in COMPLETE_SPECIFICATION] + [
        ax.formula for ax in bat.d_una().axioms
    ]
    for ssa in bat.d_ss:
        r.expect_entailment(
            f"逆向き: 完全な仕様 ∪ D_una ⊨ {ssa.statement()}",
            entails(spec_and_una, ssa.formula),
            Verdict.ENTAILED,
            ref="p.654",
            detail="行動は load, wait, shoot だけ (領域閉包) なので、行動ごとの仕様から SSA が従う",
        )

    r.expect_entailment(
        "D ⊨ dead(do(shoot, do(wait, do(load, S0))))",
        bat.entails(GOAL),
        Verdict.ENTAILED,
        ref="p.654",
    )

    # 回帰 (§16.3) でも確かめる
    reg = regress(bat, GOAL)
    for i, step in enumerate(reg.steps, start=1):
        r.formula(f"回帰 {i} 段目", step, "§16.3")
    r.expect_entailment(
        f"D_una ∪ D_S0 ⊨ {show(reg.result)} (回帰の結果)",
        entailed_by_initial_database(bat, reg.result),
        Verdict.ENTAILED,
        ref="p.664",
    )
    return r.finish()


def main() -> None:
    """コマンドラインから実行する."""
    run()


if __name__ == "__main__":
    main()
