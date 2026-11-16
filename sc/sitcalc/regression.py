"""回帰 (regression) (§16.3, p.664–665)

``φ(do([α1, ..., αn], S0))`` (do([α1, ..., αn], S0) で uniform な式) を
S0 で uniform な式 ``φ'(S0)`` に変換する:

    D ⊨ φ(do([α1, ..., αn], S0))   iff   D_una ∪ D_S0 ⊨ φ'(S0)

関数フルエントがない場合の定義 (p.664–665): φ(S0) の回帰は φ(S0)
φ(do(α, σ)) の回帰は，各関係フルエントの原子 F(t1, ..., tn, do(α, σ)) を
Φ_F(t1, ..., tn, α, σ) (SSA (16.66) の右辺) で置き換えた式の回帰

実装: 「F(t1, ..., tn, do(α, σ)) を Φ_F(t1, ..., tn, α, σ) に置き換える」一段分を，Z3 の
``substitute_funs`` で Holds を次の λ 式に置き換えることで行う:

    λp, s. if s = do(a', s') then Φ(p, a', s') else Holds(p, s)

置き換え後に ``simplify`` すると，基礎的な状況項・フルエント項についての
場合分け (``is_do(do(α, σ))`` など) が評価されて消える．これを Holds の
状況引数がすべて S0 になるまで繰り返す

本書 p.665 の手順 2 にならい，Poss の原子は先に行動前提条件公理で
Π_A に書き換える (:func:`expand_poss`)．Reiter の本 (本書の脚注 2) では
Poss を含む式の回帰も定義されている
"""

from collections.abc import Sequence
from dataclasses import dataclass

import z3

from sc.sitcalc.axioms import subterms
from sc.sitcalc.language import (
    Action,
    Fluent,
    Formula,
    Situation,
    as_datatype_term,
    as_formula,
)
from sc.sitcalc.solving import DEFAULT_TIMEOUT_MS, Entailment, entails
from sc.sitcalc.theory import BasicActionTheory

MAX_STEPS = 64


def expand_poss(theory: BasicActionTheory, phi: Formula) -> Formula:
    """Poss の原子を行動前提条件公理の右辺で置き換える (p.665 の手順 2)

    Poss(A(t1, ..., tn), σ) を Π_A(t1, ..., tn, σ) にする

    Args:
        theory: 基本行動理論
        phi: 論理式

    Returns:
        Poss を含まない同値な式 (simplify 済み)．Poss がなければ phi そのもの
    """
    lang = theory.language
    if not any(z3.is_app(e) and e.decl().eq(lang.poss_decl) for e in subterms(phi)):
        return phi
    a = Action(as_datatype_term(z3.Var(0, lang.action_sort)))
    s = Situation(as_datatype_term(z3.Var(1, lang.situation_sort)))
    replaced = z3.substitute_funs(phi, (lang.poss_decl, theory.poss_cases(a, s)))
    return as_formula(z3.simplify(replaced))


def _check_situations(theory: BasicActionTheory, phi: Formula) -> None:
    """Holds の状況引数が S0 から do で作った基礎的な項であることを確かめる

    Args:
        theory: 基本行動理論
        phi: 論理式

    Raises:
        ValueError: S0 から do で作った基礎的な項でない状況引数があるとき
    """
    lang = theory.language
    for e in subterms(phi):
        if z3.is_app(e) and e.decl().eq(lang.holds_decl):
            lang.history(Situation(as_datatype_term(e.arg(1))))  # 違えば ValueError


def _needs_regression(theory: BasicActionTheory, phi: Formula) -> bool:
    """状況引数が S0 でない Holds の原子が残っているかを判定する

    Args:
        theory: 基本行動理論
        phi: 論理式

    Returns:
        まだ回帰が必要なら True
    """
    lang = theory.language
    s0 = lang.s0.expr
    return any(
        z3.is_app(e) and e.decl().eq(lang.holds_decl) and not e.arg(1).eq(s0) for e in subterms(phi)
    )


def regress_once(theory: BasicActionTheory, phi: Formula) -> Formula:
    """回帰を一段だけ行う: F(t1, ..., tn, do(α, σ)) を Φ_F(t1, ..., tn, α, σ) に置き換えて simplify

    Args:
        theory: 基本行動理論
        phi: 論理式

    Returns:
        一段回帰した式
    """
    lang = theory.language
    # Holds の置換式を組み立てる．Var(0), Var(1) はそれぞれ Holds の第 1, 第 2 引数
    p = Fluent(as_datatype_term(z3.Var(0, lang.fluent_sort)))
    s = Situation(as_datatype_term(z3.Var(1, lang.situation_sort)))

    # Holds(p, s) の置換先: s = do(a, s') なら SSA の右辺 Φ(p, a, s')，それ以外はそのまま
    #   do_action / do_situation は do の中からそれぞれ a / s' を取り出す
    holds_replacement = z3.If(
        lang.is_do(s),
        theory.holds_cases(p, lang.do_action(s), lang.do_situation(s)),
        lang.holds(p, s),
    )

    # φ 中の Holds に置換式を適用し，具体的な状況・フルエントに応じた場合分けを簡約する
    return as_formula(z3.simplify(z3.substitute_funs(phi, (lang.holds_decl, holds_replacement))))


@dataclass(frozen=True)
class Regression:
    """回帰の結果

    Attributes:
        original: 元の式 φ(do([α1, ..., αn], S0)) (Poss を書き換えた後)
        steps: 各段の式 (steps[-1] が S0 で uniform な φ'(S0))
    """

    original: Formula
    steps: tuple[Formula, ...]

    @property
    def result(self) -> Formula:
        """φ'(S0)"""
        return self.steps[-1] if self.steps else self.original


def regress(theory: BasicActionTheory, phi: Formula) -> Regression:
    """φ を S0 で uniform な式に回帰する

    Args:
        theory: 基本行動理論
        phi: do([α1, ..., αn], S0) についての論理式

    Returns:
        各段の式と，最後の S0 で uniform な式

    Raises:
        ValueError: Holds の状況引数に S0 から作った基礎的な項でないもの (変数など) があるとき
        RuntimeError: 回帰が MAX_STEPS 段で終わらなかったとき
    """
    phi = expand_poss(theory, phi)
    _check_situations(theory, phi)
    steps: list[Formula] = []
    current = phi
    for _ in range(MAX_STEPS):
        if not _needs_regression(theory, current):
            return Regression(phi, tuple(steps))
        current = regress_once(theory, current)
        steps.append(current)
    msg = f"回帰が {MAX_STEPS} 段で終わらなかった"
    raise RuntimeError(msg)


def entailed_by_initial_database(
    theory: BasicActionTheory, phi_s0: Formula, *, timeout_ms: int = DEFAULT_TIMEOUT_MS
) -> Entailment:
    """``D_una ∪ D_S0 ⊨ φ'(S0)`` を判定する (回帰の後の手順 3)

    Args:
        theory: 基本行動理論
        phi_s0: S0 で uniform な式 (回帰の結果)
        timeout_ms: Z3 の制限時間 (ミリ秒)

    Returns:
        判定結果
    """
    premises = [ax.formula for ax in theory.d_una().axioms] + [ini.formula for ini in theory.d_s0]
    return entails(premises, phi_s0, timeout_ms=timeout_ms)


def executability_conditions(
    theory: BasicActionTheory, actions: Sequence[Action]
) -> tuple[Formula, ...]:
    """行動列 [α1, ..., αn] が S0 で実行可能であるための条件 (p.665 の手順 1)

    Poss(α1, S0), Poss(α2, do(α1, S0)), ..., Poss(αn, do([α1, ..., αn-1], S0))

    Args:
        theory: 基本行動理論
        actions: 行動列 [α1, ..., αn]

    Returns:
        n 個の Poss の原子
    """
    lang = theory.language
    conds: list[Formula] = []
    s = lang.s0
    for a in actions:
        conds.append(lang.poss(a, s))
        s = lang.do(a, s)
    return tuple(conds)
