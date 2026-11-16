"""例 4: スーツケースの問題とラミフィケーション (§16.2.2, p.657–660)

2 つの鍵 L1, L2 とばね仕掛けを持つスーツケース．両方の鍵が上がるとばねで開く
行動 flip(x) は鍵 x の上下を反転させる

1. 状態制約 (16.51) と p.658 の別の制約は論理的に同値 (区別できない)
2. 状態制約 + 直接効果 + 極小変化 では，flip(L1) の結果が曖昧 (極小モデルが 2 つ)
3. Lin の因果理論 (16.52)–(16.60) では結果が一意に決まる (open になる)
4. 因果理論から後継状態公理 (p.659) が導ける．それを使った基本行動理論は
   因果理論と同じ結論を出す (Lin [18] の「因果理論を後継状態公理にコンパイル」)
"""

import z3

from sc.sitcalc.axioms import (
    ActionPreconditionAxiom,
    InitialAxiom,
    SuccessorStateAxiom,
    forall,
)
from sc.sitcalc.causal import CausalRule, CausalTheory, CausalVocabulary
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
from sc.sitcalc.minimal import minimal_models
from sc.sitcalc.pretty import show
from sc.sitcalc.solving import Satisfiability, Verdict, entails
from sc.sitcalc.theory import BasicActionTheory
from sc.viz.export import ExampleTrace
from sc.viz.terminal import Report

# ---------------------------------------------------------------------------
# 言語
# ---------------------------------------------------------------------------


class Lock(DomainObject):
    """ソート lock の項"""

    __slots__ = ()


LOCK = enumeration("Lock", ["L1", "L2"], Lock)
L1, L2 = LOCK.constants()

LANG = SitCalcLanguage(
    "suitcase",
    actions=[Signature("flip", (LOCK,))],  # flip(x): 鍵 x の上下を反転
    fluents=[Signature("up", (LOCK,)), Signature("open")],  # up(x): 鍵 x が上, open: 開いている
)


def flip(x: Lock) -> Action:
    """鍵 x の上下を反転させる行動の項

    Args:
        x: 鍵

    Returns:
        行動の項
    """
    return LANG.actions["flip"](x)


def up(x: Lock) -> Fluent:
    """「鍵 x が上がっている」というフルエントの項

    Args:
        x: 鍵

    Returns:
        フルエントの項
    """
    return LANG.fluents["up"](x)


def open_() -> Fluent:
    """フルエント open (Python の組み込み関数名と区別するため open_)

    Returns:
        フルエントの項
    """
    return LANG.fluents["open"]()


do = LANG.do
holds = LANG.holds
S0 = LANG.s0
x = LOCK.var("x")
a = LANG.action_var("a")
s = LANG.situation_var("s")
S1 = do(flip(L1), S0)

# 初期状況 (p.657–658): 閉じていて，L1 は下，L2 は上
INITIAL = InitialAxiom(
    language=LANG,
    sentence=z3.And(z3.Not(holds(open_(), S0)), z3.Not(holds(up(L1), S0)), holds(up(L2), S0)),
    ref="p.657",
)


def constraint(sit: Situation) -> Formula:
    """状態制約 (16.51) up(L1, s) ∧ up(L2, s) ⊃ open(s) を作る

    Args:
        sit: 状況の項

    Returns:
        論理式
    """
    return z3.Implies(z3.And(holds(up(L1), sit), holds(up(L2), sit)), holds(open_(), sit))


def alternative_constraint(sit: Situation) -> Formula:
    """p.658 の別の制約 up(L1, s) ∧ ¬open(s) ⊃ ¬up(L2, s) を作る

    Args:
        sit: 状況の項

    Returns:
        論理式
    """
    return z3.Implies(
        z3.And(holds(up(L1), sit), z3.Not(holds(open_(), sit))), z3.Not(holds(up(L2), sit))
    )


# ---------------------------------------------------------------------------
# Lin の因果理論
# ---------------------------------------------------------------------------

VOCAB = CausalVocabulary(LANG)
TRUE, FALSE = VOCAB.true, VOCAB.false

RULES: tuple[CausalRule, ...] = (
    # (16.55) up(x, s) ⊃ Caused(up(x), false, do(flip(x), s))
    CausalRule(
        vocabulary=VOCAB,
        fluent=up(x),
        value=FALSE,
        situation=do(flip(x), s),
        condition=holds(up(x), s),
        variables=(x, s),
        static=False,
        ref="(16.55)",
    ),
    # (16.56) ¬up(x, s) ⊃ Caused(up(x), true, do(flip(x), s))
    CausalRule(
        vocabulary=VOCAB,
        fluent=up(x),
        value=TRUE,
        situation=do(flip(x), s),
        condition=z3.Not(holds(up(x), s)),
        variables=(x, s),
        static=False,
        ref="(16.56)",
    ),
    # (16.57) up(L1, s) ∧ up(L2, s) ⊃ Caused(open, true, s)
    CausalRule(
        vocabulary=VOCAB,
        fluent=open_(),
        value=TRUE,
        situation=s,
        condition=z3.And(holds(up(L1), s), holds(up(L2), s)),
        variables=(s,),
        static=True,
        ref="(16.57)",
        note="ばね仕掛けを因果規則として表す (静的な規則)",
    ),
)


def book_up_ssa() -> Formula:
    """p.659: up(x, do(a, s)) ≡ (a = flip(x) ∧ ¬up(x, s)) ∨ (up(x, s) ∧ a ≠ flip(x))

    Returns:
        全称閉包した文
    """
    return forall(
        [x, a, s],
        holds(up(x), do(a, s))
        == z3.Or(
            z3.And(eq(a, flip(x)), z3.Not(holds(up(x), s))), z3.And(holds(up(x), s), ne(a, flip(x)))
        ),
    )


def book_open_ssa() -> Formula:
    """p.659 の open の後継状態公理

    Returns:
        全称閉包した文
    """
    return forall(
        [a, s],
        holds(open_(), do(a, s))
        == z3.Or(
            z3.And(eq(a, flip(L1)), z3.Not(holds(up(L1), s)), holds(up(L2), s)),
            z3.And(eq(a, flip(L2)), z3.Not(holds(up(L2), s)), holds(up(L1), s)),
            holds(open_(), s),
        ),
    )


def pseudo_ssa() -> Formula:
    """擬似後継状態公理 (16.61)

    Holds(p, do(a, s)) ≡ Caused(p, true, do(a, s)) ∨ Holds(p, s) ∧ ¬Caused(p, false, do(a, s))

    Returns:
        全称閉包した文
    """
    p = LANG.fluent_var("p")
    after = do(a, s)
    return forall(
        [p, a, s],
        holds(p, after)
        == z3.Or(
            VOCAB.caused(p, TRUE, after), z3.And(holds(p, s), z3.Not(VOCAB.caused(p, FALSE, after)))
        ),
    )


def compiled_basic_action_theory() -> BasicActionTheory:
    """因果理論から導いた後継状態公理 (p.659) を使う基本行動理論を作る

    Lin [18] の「因果理論を後継状態公理にコンパイルする」にあたる

    Returns:
        基本行動理論 (D_S0 は初期状況 p.657)
    """
    up_ssa = SuccessorStateAxiom(
        language=LANG,
        fluent=LANG.fluents["up"],
        params=(x,),
        action=a,
        situation=s,
        phi=z3.Or(
            z3.And(eq(a, flip(x)), z3.Not(holds(up(x), s))),
            z3.And(holds(up(x), s), ne(a, flip(x))),
        ),
        ref="p.659",
    )
    open_ssa = SuccessorStateAxiom(
        language=LANG,
        fluent=LANG.fluents["open"],
        params=(),
        action=a,
        situation=s,
        phi=z3.Or(
            z3.And(eq(a, flip(L1)), z3.Not(holds(up(L1), s)), holds(up(L2), s)),
            z3.And(eq(a, flip(L2)), z3.Not(holds(up(L2), s)), holds(up(L1), s)),
            holds(open_(), s),
        ),
        ref="p.659",
    )
    always_possible = ActionPreconditionAxiom(
        language=LANG,
        action_symbol=LANG.actions["flip"],
        params=(x,),
        situation=s,
        pi=z3.BoolVal(True),
        ref="—",
        note="本書には前提条件の記述がないので、常に実行可能とした",
    )
    return BasicActionTheory(
        name="スーツケース (因果理論からコンパイル)",
        language=LANG,
        d_ss=[up_ssa, open_ssa],
        d_ap=[always_possible],
        d_s0=[INITIAL],
    )


def _decided_value(theory: CausalTheory, phi: Formula) -> str:
    """理論から論理式の真偽が決まるかを調べる

    Args:
        theory: 因果理論
        phi: 論理式

    Returns:
        φ が帰結すれば ``"T"``，¬φ が帰結すれば ``"F"``，どちらでもなければ ``"未決定"``
    """
    if theory.entails(phi).entailed:
        return "T"
    if theory.entails(z3.Not(phi)).entailed:
        return "F"
    return "未決定"


# 画面に出す説明文
SAME_CONSTRAINT_NOTE = (
    "物理的に違う仕掛けが同じ状態制約になる。状態制約だけでは間接効果の向きが表せない"
)
MINIMAL_CHANGE_NOTE = (
    "直接効果 (flip(L1) で L1 が上がる) と、S0 と S1 = do(flip(L1), S0) での状態制約 (16.51) を"
    "満たすモデルのうち、S0 から S1 で値が変わるフルエントの集合が極小なものを列挙する。"
)
AMBIGUOUS_NOTE = "「スーツケースが開く」と「L2 が下がる」のどちらも極小。直観どおりなのは前者"

# S1 = do(flip(L1), S0) で期待する値: L1 が上がり (直接効果)，ばねで開き (間接効果)，L2 は上のまま
EXPECTED_AT_S1 = {up(L1): "T", up(L2): "T", open_(): "T"}


def run() -> ExampleTrace:
    """例題を実行する

    Returns:
        この例題の記録 (ビューア用．検査結果を含む)

    Raises:
        CheckFailedError: 期待と違う検査があったとき (記録は例外の ``trace`` に入る)
    """
    r = Report("suitcase", "例 4: スーツケースの問題 (ラミフィケーション)", "§16.2.2 (p.657–660)")

    r.section("言語と初期状況", "p.657")
    r.text("ソート: lock = {L1, L2}。行動: flip(x)。フルエント: up(x), open。")
    r.axiom_list("初期状況", "p.657", [INITIAL])

    _check_equivalent_constraints(r)
    _check_minimal_change(r)
    theory = _check_causal_theory(r)
    _check_derived_ssa(r)
    _check_compiled_theory(r, theory)

    return r.finish()


def _check_equivalent_constraints(r: Report) -> None:
    """1. 状態制約 (16.51) と p.658 の別の制約が論理的に同値であることを確かめる

    Args:
        r: 出力先のレポート
    """
    r.section("1. 状態制約 (16.51) と、論理的に同値な別の制約", "(16.51), p.658")
    r.formula("(16.51)", constraint(s), "(16.51)")
    r.formula("p.658 の別の制約 (L2 を下げる仕掛け)", alternative_constraint(s), "p.658")

    equivalent = entails([], forall([s], constraint(s) == alternative_constraint(s)))
    r.expect_entailment(
        "∀s. (16.51) ≡ p.658 の制約",
        equivalent,
        Verdict.ENTAILED,
        ref="p.658",
        detail=SAME_CONSTRAINT_NOTE,
    )


def _check_minimal_change(r: Report) -> None:
    """2. 状態制約 + 直接効果 + 極小変化 では flip(L1) の結果が曖昧なことを確かめる

    Args:
        r: 出力先のレポート
    """
    r.section("2. 状態制約 + 直接効果 + 極小変化", "p.657–658")
    r.text(MINIMAL_CHANGE_NOTE)

    # 初期状況，S0 と S1 での状態制約，flip(L1) の直接効果 (S0 で L1 は下なので上がる)
    premises = [INITIAL.formula, constraint(S0), constraint(S1), holds(up(L1), S1)]

    # 「S0 から S1 で値が変わった」という原子を最小化する
    fluents = LANG.ground_fluents()
    change_atoms = [z3.Not(holds(f, S1) == holds(f, S0)) for f in fluents]
    models = sorted(minimal_models(premises, change_atoms), key=lambda mm: mm.true_atoms)

    # 極小モデルごとに，変化したフルエントと S1 の状態を表にする
    rows = [
        [
            f"#{i + 1}",
            ", ".join(show(fluents[j].expr) for j in mm.true_atoms),
            ", ".join(f"{show(f.expr)}={'T' if mm.truth(holds(f, S1)) else 'F'}" for f in fluents),
        ]
        for i, mm in enumerate(models)
    ]
    r.table("極小変化のモデル", ["", "変化したフルエント", "S1 = do(flip(L1), S0) の状態"], rows)

    r.expect(
        "極小変化のモデルの個数",
        ok=len(models) == 2,  # noqa: PLR2004
        actual=f"{len(models)} 個",
        expected="2 個 (開く / L2 が下がる)",
        ref="p.658",
        detail=AMBIGUOUS_NOTE,
    )


def _check_causal_theory(r: Report) -> CausalTheory:
    """3. Lin の因果理論では flip(L1) の結果が一意に決まることを確かめる

    Args:
        r: 出力先のレポート

    Returns:
        初期状況つきの因果理論
    """
    r.section("3. Lin の因果理論", "(16.52)–(16.60)")
    theory = CausalTheory(name="スーツケース", vocabulary=VOCAB, rules=RULES, d_s0=[INITIAL])
    for title, ref, axioms in theory.groups():
        r.axiom_list(title, ref, axioms)

    # S1 での各フルエントの値が理論から決まる
    for f in LANG.ground_fluents():
        decided = _decided_value(theory, holds(f, S1))
        r.expect(
            f"{show(holds(f, S1))} の値",
            ok=decided == EXPECTED_AT_S1[f],
            actual=decided,
            expected=EXPECTED_AT_S1[f],
            ref="p.658",
            detail="因果理論から値が一意に決まる" if decided != "未決定" else "",
        )

    # 状態制約 (16.51) は，静的な因果規則 (16.57) と (16.52) から任意の状況で従う
    constraint_holds = theory.entails(forall([s], constraint(s)))
    r.expect_entailment(
        "(16.51) が任意の状況で従う: T ⊨ ∀s. up(L1, s) ∧ up(L2, s) ⊃ open(s)",
        constraint_holds,
        Verdict.ENTAILED,
        ref="p.658",
        detail="静的な因果規則 (16.57) と (16.52) から",
    )
    return theory


def _check_derived_ssa(r: Report) -> None:
    """4. 因果理論から (擬似) 後継状態公理 (16.61), p.659 が導けることを確かめる

    Args:
        r: 出力先のレポート
    """
    r.section("4. 因果理論から後継状態公理へ", "(16.61), p.659")
    generic = CausalTheory(name="スーツケース (D_S0 なし)", vocabulary=VOCAB, rules=RULES)

    for label, ref, phi in (
        ("擬似後継状態公理 (16.61)", "(16.61)", pseudo_ssa()),
        ("up の後継状態公理", "p.659", book_up_ssa()),
        ("open の後継状態公理", "p.659", book_open_ssa()),
    ):
        r.formula(label, phi, ref)
        result = generic.entails(phi)
        r.expect_entailment(f"T ⊨ {label}", result, Verdict.ENTAILED, ref=ref)


def _check_compiled_theory(r: Report, theory: CausalTheory) -> None:
    """5. 導いた後継状態公理の基本行動理論が，因果理論と同じ結論を出すことを確かめる

    Args:
        r: 出力先のレポート
        theory: 初期状況つきの因果理論 (比較用)
    """
    r.section("5. 後継状態公理による基本行動理論", "p.659")
    bat = compiled_basic_action_theory()
    r.theory(bat)

    # 定理 16.1
    relative = bat.relative_satisfiability()
    r.expect_sat(
        "定理 16.1: D_una ∪ D_S0 は充足可能", relative, Satisfiability.SAT, ref="Theorem 16.1"
    )

    # flip(L1) の後: 開いていて，L2 は上のまま
    after_flip = bat.entails(z3.And(holds(open_(), S1), holds(up(L2), S1)))
    r.expect_entailment(
        "D ⊨ open(do(flip(L1), S0)) ∧ up(L2, do(flip(L1), S0))",
        after_flip,
        Verdict.ENTAILED,
        ref="p.659",
    )

    # 一度開いたら，鍵を動かしても開いたまま (基本行動理論と因果理論の両方で)
    final = LANG.do_sequence([flip(L1), flip(L1), flip(L2)])
    by_bat = bat.entails(holds(open_(), final))
    r.expect_entailment(
        "D ⊨ open(do([flip(L1), flip(L1), flip(L2)], S0)) (一度開いたら開いたまま)",
        by_bat,
        Verdict.ENTAILED,
        ref="p.659",
    )
    by_causal = theory.entails(holds(open_(), final))
    r.expect_entailment(
        "因果理論でも同じ: T ⊨ open(do([flip(L1), flip(L1), flip(L2)], S0))",
        by_causal,
        Verdict.ENTAILED,
        ref="p.659",
    )


def main() -> None:
    """コマンドラインから実行する"""
    run()


if __name__ == "__main__":
    main()
