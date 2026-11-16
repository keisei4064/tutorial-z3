"""帰結 (entailment) の判定とモデル探索

一階論理の帰結 ``T ⊨ φ`` は「T ∪ {¬φ} が充足不能」と同値なので，Z3 で
``T ∪ {¬φ}`` を解いて判定する:

- unsat   → 帰結する (ENTAILED)
- sat     → 帰結しない．モデルが反例 (NOT_ENTAILED)
- unknown → 判定できなかった (UNKNOWN)．量化子を含む理論では起こりうる
"""

from collections.abc import Sequence
from dataclasses import dataclass
from enum import Enum

import z3

from sc.sitcalc.language import Formula
from sc.sitcalc.simplify import expand_finite_quantifiers

DEFAULT_TIMEOUT_MS = 20_000


class Verdict(Enum):
    """帰結判定の結果

    Attributes:
        ENTAILED: 帰結する (T ∪ {¬φ} が unsat)
        NOT_ENTAILED: 帰結しない (T ∪ {¬φ} が sat．モデルが反例)
        UNKNOWN: Z3 が判定できなかった (timeout など)
    """

    ENTAILED = "帰結する (unsat)"
    NOT_ENTAILED = "帰結しない (sat: 反例あり)"
    UNKNOWN = "判定不能 (unknown)"


@dataclass(frozen=True)
class Entailment:
    """``T ⊨ φ`` の判定結果

    Attributes:
        verdict: 結果
        countermodel: NOT_ENTAILED のときの反例 (T ∪ {¬φ} のモデル)
        reason: UNKNOWN のときの Z3 の理由 (timeout など)

    """

    verdict: Verdict
    countermodel: z3.ModelRef | None = None
    reason: str = ""

    @property
    def entailed(self) -> bool:
        """帰結したか"""
        return self.verdict is Verdict.ENTAILED


def entails(
    premises: Sequence[Formula],
    conclusion: Formula,
    *,
    timeout_ms: int = DEFAULT_TIMEOUT_MS,
    expand_finite: bool = False,
) -> Entailment:
    """``premises ⊨ conclusion`` を判定する

    ``premises ∪ {¬conclusion}`` を Z3 で解く．unsat なら帰結し，sat ならモデルが反例

    Args:
        premises: 前提 (理論)
        conclusion: 結論
        timeout_ms: Z3 の制限時間 (ミリ秒)
        expand_finite: 列挙型のソート上の量化子を連言・選言に展開してから解くか
            (:func:`sc.sitcalc.simplify.expand_finite_quantifiers`．同値な書き換え)

    Returns:
        判定結果 (反例モデルや unknown の理由を含む)
    """
    if expand_finite:
        premises = [expand_finite_quantifiers(p) for p in premises]
        conclusion = expand_finite_quantifiers(conclusion)
    solver = z3.Solver()
    solver.set(timeout=timeout_ms)
    solver.add(*premises)
    solver.add(z3.Not(conclusion))
    result = solver.check()
    if result == z3.unsat:
        return Entailment(Verdict.ENTAILED)
    if result == z3.sat:
        return Entailment(Verdict.NOT_ENTAILED, countermodel=solver.model())
    return Entailment(Verdict.UNKNOWN, reason=solver.reason_unknown())


class Satisfiability(Enum):
    """充足可能性の判定結果

    Attributes:
        SAT: 充足可能
        UNSAT: 充足不能
        UNKNOWN: Z3 が判定できなかった
    """

    SAT = "充足可能 (sat)"
    UNSAT = "充足不能 (unsat)"
    UNKNOWN = "判定不能 (unknown)"


@dataclass(frozen=True)
class SatResult:
    """充足可能性の判定結果とモデル

    Attributes:
        status: 結果
        model: SAT のときのモデル
        reason: UNKNOWN のときの Z3 の理由 (timeout など)
    """

    status: Satisfiability
    model: z3.ModelRef | None = None
    reason: str = ""


def satisfiable(formulas: Sequence[Formula], *, timeout_ms: int = DEFAULT_TIMEOUT_MS) -> SatResult:
    """``formulas`` が充足可能かを判定する

    Args:
        formulas: 論理式の集まり
        timeout_ms: Z3 の制限時間 (ミリ秒)

    Returns:
        判定結果 (sat ならモデルを含む)
    """
    solver = z3.Solver()
    solver.set(timeout=timeout_ms)
    solver.add(*formulas)
    result = solver.check()
    if result == z3.sat:
        return SatResult(Satisfiability.SAT, model=solver.model())
    if result == z3.unsat:
        return SatResult(Satisfiability.UNSAT)
    return SatResult(Satisfiability.UNKNOWN, reason=solver.reason_unknown())
