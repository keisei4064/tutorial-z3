"""例 3: ブロック世界の 2 つ目の版 — 行動 move だけ (§16.1, (16.25)–(16.27))

本書 p.650: 「エージェントがブロックを clear な位置から別の clear な位置へ動かせるなら
必要な行動は move(x, y) だけ (位置はブロックまたは机)」．フルエントも on(x, y) と
clear(x) の 2 つで足りる

1. 基本行動理論 (16.25)–(16.27)
2. プランニング: 例 2 と同じ Sussman の異常が 3 手で解ける (例 2 では 6 手)
3. 注意: (16.25) には x ≠ y がないので，move(B, B) (ブロックを自分の上に置く) が
   実行可能になってしまう
"""

import z3

from sc.sitcalc.axioms import ActionPreconditionAxiom, SuccessorStateAxiom, closed_initial_database
from sc.sitcalc.language import (
    Action,
    DomainObject,
    Fluent,
    Formula,
    Signature,
    SitCalcLanguage,
    Situation,
    enumeration,
    eq,
    ne,
)
from sc.sitcalc.planning import find_plan
from sc.sitcalc.pretty import show
from sc.sitcalc.solving import Satisfiability, Verdict
from sc.sitcalc.theory import BasicActionTheory
from sc.viz.export import ExampleTrace, StateTrace
from sc.viz.terminal import Report, towers_text
from sc.viz.tree import situation_tree

# ---------------------------------------------------------------------------
# 言語: 位置 (ブロックまたは机) のソートを 1 つにまとめる (本書の table も同じソートの定数)
# ---------------------------------------------------------------------------


class Position(DomainObject):
    """位置: ブロックまたは机 (table)"""

    __slots__ = ()


POSITION = enumeration("Position", ["A", "B", "C", "table"], Position)
A, B, C, TABLE = POSITION.constants()
BLOCKS = (A, B, C)

LANG = SitCalcLanguage(
    "blocks_move",
    actions=[Signature("move", (POSITION, POSITION))],  # move(x, y): x を位置 y へ動かす
    fluents=[
        Signature("on", (POSITION, POSITION)),  # on(x, y): x が y の上にある
        Signature("clear", (POSITION,)),  # clear(x): x の上に何もない
    ],
)


def move(x: Position, y: Position) -> Action:
    """ブロック x を位置 y へ動かす行動の項

    Args:
        x: 動かすブロック x
        y: 移動先 (ブロックまたは table)

    Returns:
        行動の項
    """
    return LANG.actions["move"](x, y)


def on(x: Position, y: Position) -> Fluent:
    """「x が y の上にある」というフルエントの項

    Args:
        x: ブロック x
        y: 位置 y (ブロックまたは table)

    Returns:
        フルエントの項
    """
    return LANG.fluents["on"](x, y)


def clear(x: Position) -> Fluent:
    """「x の上に何もない」というフルエントの項

    Args:
        x: 位置 x (ブロックまたは table)

    Returns:
        フルエントの項
    """
    return LANG.fluents["clear"](x)


do = LANG.do
holds = LANG.holds
S0 = LANG.s0
x, y, u, v = POSITION.vars("x", "y", "u", "v")
a = LANG.action_var("a")
s = LANG.situation_var("s")

# ---------------------------------------------------------------------------
# 公理 (16.25)–(16.27)
# ---------------------------------------------------------------------------

# (16.25) Poss(move(x, y), s) ≡ x ≠ table ∧ clear(x, s) ∧ clear(y, s)
D_AP = (
    ActionPreconditionAxiom(
        language=LANG,
        action_symbol=LANG.actions["move"],
        params=(x, y),
        situation=s,
        pi=z3.And(ne(x, TABLE), holds(clear(x), s), holds(clear(y), s)),
        ref="(16.25)",
    ),
)

# 本書の (16.26), (16.27) は「a = move(x, y) のとき」の形で書かれている．行動は move だけ
# なので，∃x, y. a = move(x, y) ∧ … とすれば後継状態公理 (16.66) の形になる
D_SS = (
    # (16.26) clear(u, do(move(x, y), s)) ≡ u = table ∨ on(x, u, s) ∨ (clear(u, s) ∧ u ≠ y)
    SuccessorStateAxiom(
        language=LANG,
        fluent=LANG.fluents["clear"],
        params=(u,),
        action=a,
        situation=s,
        phi=z3.Exists(
            [x.expr, y.expr],
            z3.And(
                eq(a, move(x, y)),
                z3.Or(eq(u, TABLE), holds(on(x, u), s), z3.And(holds(clear(u), s), ne(u, y))),
            ),
        ),
        ref="(16.26)",
    ),
    # (16.27) on(u, v, do(move(x, y), s)) ≡ (x = u ∧ y = v) ∨ (on(u, v, s) ∧ u ≠ x)
    SuccessorStateAxiom(
        language=LANG,
        fluent=LANG.fluents["on"],
        params=(u, v),
        action=a,
        situation=s,
        phi=z3.Exists(
            [x.expr, y.expr],
            z3.And(
                eq(a, move(x, y)),
                z3.Or(z3.And(eq(x, u), eq(y, v)), z3.And(holds(on(u, v), s), ne(u, x))),
            ),
        ),
        ref="(16.27)",
    ),
)

SUSSMAN_INITIAL = closed_initial_database(
    LANG,
    [on(C, A), on(A, TABLE), on(B, TABLE), clear(C), clear(B), clear(TABLE)],
    ref="—",
    note="Sussman の異常 (例 2 と同じ配置)。机はいつでも clear",
)

BAT = BasicActionTheory(
    name="ブロック世界 move 版 (Sussman の異常)",
    language=LANG,
    d_ss=D_SS,
    d_ap=D_AP,
    d_s0=SUSSMAN_INITIAL,
)


def sussman_goal(sit: Situation) -> Formula:
    """ゴール on(A, B) ∧ on(B, C) を作る

    Args:
        sit: 状況の項

    Returns:
        論理式
    """
    return z3.And(holds(on(A, B), sit), holds(on(B, C), sit))


def state_trace(state: frozenset[Fluent]) -> StateTrace:
    """真なフルエントの集合から塔の形を作る (自分の上に載ったブロックは塔に含めない)

    Args:
        state: 真な基礎的なフルエントの集合

    Returns:
        ビューア用の状態 (この版にはロボットの手がないので holding は常に None)
    """
    above: dict[str, str] = {}
    for b1 in BLOCKS:
        for b2 in BLOCKS:
            if b1 != b2 and on(b1, b2) in state:
                above[str(b2)] = str(b1)
    towers: list[list[str]] = []
    for b in BLOCKS:
        if on(b, TABLE) in state:
            tower = [str(b)]
            while tower[-1] in above:
                tower.append(above[tower[-1]])
            towers.append(tower)
    return {"towers": towers, "holding": None, "fluents": sorted(show(f.expr) for f in state)}


def run() -> ExampleTrace:
    """例題を実行する

    Returns:
        この例題の記録 (ビューア用．検査結果を含む)

    Raises:
        CheckFailedError: 期待と違う検査があったとき (記録は例外の ``trace`` に入る)
    """
    r = Report("blocks_world_move", "例 3: ブロック世界 (move 版)", "§16.1 (16.25)–(16.27)")

    r.section("1. 基本行動理論", "(16.25)–(16.27)")
    r.text(
        "ソート: 位置 = {A, B, C, table} (ブロックと机)。行動: move(x, y)。"
        "フルエント: on(x, y), clear(x)。"
    )
    r.theory(BAT)
    r.expect_sat(
        "定理 16.1: D_una ∪ D_S0 は充足可能",
        BAT.relative_satisfiability(),
        Satisfiability.SAT,
        ref="Theorem 16.1",
    )

    r.section("2. プランニング: Sussman の異常", "§16.4")
    compiled = BAT.compile()
    evaluator = compiled.evaluator()
    r.text("初期状況:\n" + towers_text(state_trace(evaluator.state(S0))))
    result = find_plan(compiled, sussman_goal, max_length=6)
    r.table(
        "反復深化",
        ["n", "結果", "秒"],
        [[str(at.length), at.status, f"{at.seconds:.2f}"] for at in result.attempts],
    )
    plan = result.plan
    r.expect(
        "最短プランの長さ",
        ok=plan is not None and len(plan) == 3,  # noqa: PLR2004
        actual="見つからない" if plan is None else f"{len(plan)} 手: [{', '.join(map(str, plan))}]",
        expected="3 手 (例 2 の stack/unstack/pickup/putdown 版では 6 手)",
        ref="§16.4",
    )
    if plan is not None:
        sit = S0
        for i, act in enumerate(plan, start=1):
            sit = do(act, sit)
            r.text(f"{i}. {act}\n" + towers_text(state_trace(evaluator.state(sit))))
        plan_situation = LANG.do_sequence(plan)
        r.expect_entailment(
            "検証 (公理版): D ⊨ Executable(S0, s_plan) ∧ on(A, B, s_plan) ∧ on(B, C, s_plan)",
            BAT.entails(z3.And(LANG.executable(S0, plan_situation), sussman_goal(plan_situation))),
            Verdict.ENTAILED,
            ref="p.662",
        )
        r.situation_tree(
            {
                "kind": "situation_tree",
                "title": "move 版 Sussman の異常: 状況の木とプラン",
                "goal": "on(A, B) ∧ on(B, C)",
                "plan": [str(act) for act in plan],
                "nodes": situation_tree(evaluator, plan, sussman_goal, state_trace, depth=2),
            }
        )

    r.section("3. 注意: (16.25) には x ≠ y がない", "(16.25)")
    r.expect_entailment(
        "D ⊨ Poss(move(B, B), S0)",
        BAT.entails(LANG.poss(move(B, B), S0)),
        Verdict.ENTAILED,
        ref="(16.25)",
        detail="B は clear なので、x = y = B で前提条件が満たされる",
    )
    r.expect_entailment(
        "D ⊨ on(B, B, do(move(B, B), S0))",
        BAT.entails(holds(on(B, B), do(move(B, B), S0))),
        Verdict.ENTAILED,
        ref="(16.27)",
        detail="ブロックが自分自身の上に載る。前提条件に x ≠ y を加えるべき",
    )
    return r.finish()


def main() -> None:
    """コマンドラインから実行する"""
    run()


if __name__ == "__main__":
    main()
