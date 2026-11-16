"""状況の木 (§16.3 p.662: 状況の領域は S0 を根とする木) をビューア用に作る

Reiter の基礎公理のもとでは，状況は行動列と 1 対 1 に対応し，状況全体は
S0 を根として各状況 s から行動 a ごとに子 do(a, s) が出る木をなす (p.662)
ここでは実行可能な (Poss が真の) 行動の枝だけを，指定した深さまで広げる
同じ状態に至る別の行動列も，別の状況 (別の節点) として扱う点に注意
"""

from collections.abc import Callable, Sequence

from sc.sitcalc.language import Action, Fluent, Formula, Situation
from sc.sitcalc.pretty import show
from sc.sitcalc.theory import Evaluator
from sc.viz.export import SituationNodeTrace, StateTrace


def situation_tree(
    evaluator: Evaluator,
    plan: Sequence[Action],
    goal: Callable[[Situation], Formula],
    state_trace: Callable[[frozenset[Fluent]], StateTrace],
    *,
    depth: int,
) -> list[SituationNodeTrace]:
    """S0 から実行可能な行動で depth 段まで広げた木と，プランの経路 (深さ制限を超えても含める)

    Args:
        evaluator: コンパイルした理論の評価器
        plan: プラン (経路の節点には on_plan を付ける)
        goal: ゴール G(s) (各節点で達成しているかを記録する)
        state_trace: 真なフルエントの集合から，ビューア用の状態を作る関数
        depth: すべての枝を広げる深さ

    Returns:
        節点のリスト (幅優先の順．根 S0 の id は 0)
    """
    lang = evaluator.compiled.theory.language
    nodes: list[SituationNodeTrace] = []
    plan_prefixes = {tuple(plan[:i]) for i in range(len(plan) + 1)}

    def add(
        sit: Situation, parent: int | None, action: Action | None, hist: tuple[Action, ...]
    ) -> int:
        """節点を 1 つ追加する

        Args:
            sit: 状況の項
            parent: 親の節点の id (根なら None)
            action: 親からの行動 (根なら None)
            hist: S0 からの行動列

        Returns:
            追加した節点の id
        """
        node: SituationNodeTrace = {
            "id": len(nodes),
            "parent": parent,
            "action": None if action is None else str(action),
            "term": show(sit.expr),
            "depth": len(hist),
            "state": state_trace(evaluator.state(sit)),
            "possible": [str(act) for act in evaluator.executable_actions(sit)],
            "on_plan": hist in plan_prefixes,
            "goal": evaluator.truth(goal(sit)),
        }
        nodes.append(node)
        return node["id"]

    queue: list[tuple[Situation, int, tuple[Action, ...]]] = [
        (lang.s0, add(lang.s0, None, None, ()), ())
    ]
    while queue:
        sit, node_id, hist = queue.pop(0)
        for act in evaluator.executable_actions(sit):
            child_hist = (*hist, act)
            if len(child_hist) > depth and child_hist not in plan_prefixes:
                continue
            child = lang.do(act, sit)
            queue.append((child, add(child, node_id, act, child_hist), child_hist))
    return nodes
