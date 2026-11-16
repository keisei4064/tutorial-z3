"""状況計算によるプランニング (§16.4, p.665–666, p.662)

Green の定式化 (p.666): 状況計算の理論 T とゴール G について

    T ⊨ ∃s. G(s)

を構成的に示せれば，証人の状況項 s = do([α1, ..., αn], S0) からプランが読み取れる
Reiter の基礎公理のもとでは「ゴールが達成可能」は (p.662)

    ∃s'. S0 ⊑ s' ∧ Holds(g, s') ∧ Executable(S0, s')

と書ける．ここではプランの長さ n を 0, 1, 2, ... と増やし，行動を記号定数 α1, ..., αn
とした状況 do([α1, ..., αn], S0) について

    Executable(S0, do([α1, ..., αn], S0)) ∧ G(do([α1, ..., αn], S0))

が充足可能かを Z3 で調べる (有界の反復深化)．最初に sat になった長さのモデルの
α1, ..., αn がプランで，それより短いプランはない (それまでの長さは unsat)

モデルを探す問題なので，理論は :meth:`BasicActionTheory.compile` で再帰関数に
コンパイルしたものを使う (公理のままだと量化子のため Z3 が unknown を返しやすい)
"""

import time
from collections.abc import Callable
from dataclasses import dataclass

import z3

from sc.sitcalc.language import Action, Formula, Situation
from sc.sitcalc.theory import CompiledTheory


@dataclass(frozen=True)
class Attempt:
    """ある長さでの探索結果

    Attributes:
        length: プランの長さ n
        status: Z3 の結果 (``"sat"`` / ``"unsat"`` / ``"unknown"``)
        seconds: かかった秒数
    """

    length: int
    status: str
    seconds: float


@dataclass(frozen=True)
class PlanningResult:
    """プランニングの結果

    Attributes:
        plan: 見つかったプラン (最短)．見つからなければ None
        attempts: 各長さでの探索結果

    """

    plan: tuple[Action, ...] | None
    attempts: tuple[Attempt, ...]


def find_plan(
    compiled: CompiledTheory,
    goal: Callable[[Situation], Formula],
    *,
    max_length: int = 10,
    timeout_ms: int = 120_000,
) -> PlanningResult:
    """最短のプランを反復深化で探す

    Args:
        compiled: 再帰関数にコンパイルした基本行動理論
        goal: ゴール G(s) (状況を受け取って論理式を返す)
        max_length: 探すプランの最大長
        timeout_ms: 各長さでの Z3 の制限時間

    Returns:
        最短のプランと，各長さでの探索結果
    """
    lang = compiled.theory.language
    attempts: list[Attempt] = []
    for n in range(max_length + 1):
        alphas = [lang.action_var(f"α{i + 1}") for i in range(n)]
        s_n = lang.do_sequence(alphas)
        solver = z3.Solver()
        solver.set(timeout=timeout_ms)
        solver.add(compiled.translate(z3.And(lang.executable(lang.s0, s_n), goal(s_n))))
        start = time.perf_counter()
        result = solver.check()
        elapsed = time.perf_counter() - start
        status = "sat" if result == z3.sat else "unsat" if result == z3.unsat else "unknown"
        attempts.append(Attempt(n, status, elapsed))
        if result == z3.sat:
            model = solver.model()
            plan = tuple(
                lang.lift_action(model.eval(al.expr, model_completion=True)) for al in alphas
            )
            return PlanningResult(plan, tuple(attempts))
        if result != z3.unsat:
            break
    return PlanningResult(None, tuple(attempts))
