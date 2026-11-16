"""極小モデルの列挙 (有限の原子に制限したサーカムスクリプション)

§16.2 で扱う McCarthy の一般フレーム公理 (16.28) は，述語 abnormal を
サーカムスクリプション (circumscription, 本書 Chapter 6) で最小化して使う
サーカムスクリプションのモデルは「abnormal の外延が包含について極小なモデル」
(他の述語は可変) である

一般のサーカムスクリプションは二階の式なので Z3 では扱えない．ここでは
最小化する原子を有限個 (関心のある状況での abnormal の基礎原子) に限り
その範囲で包含について極小なモデルを列挙する．Hanks–McDermott の例 (p.654) や
スーツケースの例 (p.657–658) の「極小変化が曖昧になる」現象を見るには十分である

アルゴリズム: モデルを 1 つ見つけ，真の原子の集合を真部分集合に縮められなくなるまで
縮める (極小化)．得られた極小集合の上位集合を禁止して，これを繰り返す
"""

from collections.abc import Sequence
from dataclasses import dataclass

import z3

from sc.sitcalc.language import Formula


@dataclass(frozen=True)
class MinimalModel:
    """極小モデル

    Attributes:
        true_atoms: 真になっている (最小化対象の) 原子の添字
        model: Z3 のモデル (他の述語の値を調べるのに使う)

    """

    true_atoms: tuple[int, ...]
    model: z3.ModelRef

    def truth(self, phi: Formula) -> bool:
        """このモデルでの論理式の真偽を返す

        Args:
            phi: 論理式 (モデルにない記号は model completion で補う)

        Returns:
            真なら True
        """
        return z3.is_true(self.model.eval(phi, model_completion=True))


def minimal_models(
    premises: Sequence[Formula], atoms: Sequence[Formula], *, limit: int = 64
) -> list[MinimalModel]:
    """前提のモデルのうち，atoms の真の集合が包含について極小なものをすべて列挙する

    Args:
        premises: 理論
        atoms: 最小化する原子 (Bool の式)
        limit: 列挙する極小モデルの上限

    Returns:
        極小モデル (極小な真の集合ごとに代表のモデルを 1 つ)

    Raises:
        RuntimeError: Z3 が sat/unsat を決められなかった，または上限を超えたとき
    """
    solver = z3.Solver()
    solver.add(*premises)
    found: list[MinimalModel] = []
    while True:
        result = solver.check()
        if result != z3.sat:
            if result != z3.unsat:
                msg = f"極小モデルの列挙中に Z3 が {result} を返した"
                raise RuntimeError(msg)
            return found
        model = solver.model()
        true = _true_set(model, atoms)
        while True:  # 極小化: 真の集合を真部分集合に縮められる限り縮める
            solver.push()
            solver.add(*(z3.Not(atoms[i]) for i in range(len(atoms)) if i not in true))
            solver.add(_some_false(atoms, true))
            if solver.check() == z3.sat:
                model = solver.model()
                true = _true_set(model, atoms)
                solver.pop()
                continue
            solver.pop()
            break
        found.append(MinimalModel(tuple(sorted(true)), model))
        if len(found) >= limit:
            msg = f"極小モデルが {limit} 個を超えた"
            raise RuntimeError(msg)
        solver.add(_some_false(atoms, true))  # この極小集合の上位集合を禁止


def _true_set(model: z3.ModelRef, atoms: Sequence[Formula]) -> set[int]:
    """モデルで真になっている原子の添字を集める

    Args:
        model: Z3 のモデル
        atoms: 原子

    Returns:
        真の原子の添字の集合
    """
    return {i for i, at in enumerate(atoms) if z3.is_true(model.eval(at, model_completion=True))}


def _some_false(atoms: Sequence[Formula], true: set[int]) -> Formula:
    """「true の原子のどれかが偽」という式を作る

    Args:
        atoms: 原子
        true: 原子の添字の集合

    Returns:
        ``⋁ ¬atoms[i]`` (true が空なら偽)
    """
    if not true:
        return z3.BoolVal(False)
    return z3.Or(*(z3.Not(atoms[i]) for i in sorted(true)))
