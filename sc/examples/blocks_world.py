"""例 2: ブロック世界 (§16.1 の 1 つ目の版, §16.2.1, §16.3, §16.4).

片手のロボットが、同じ大きさのブロックを机の上で塔に積み替える (p.649–650)。

1. 言語 (p.650) と、効果の完全な仕様 (16.1)–(16.24)
2. Reiter の手続き: 効果公理 (16.32)–(16.49) から後継状態公理 (16.50) を作る
   (p.656 の clear の後継状態公理と一致することも確かめる)
3. 整合性の仮定 ¬(γ⁺ ∧ γ⁻) (p.656) は clear について無条件では成り立たない
   (a = stack(u, u) が反例)。Poss と状態制約のもとでは成り立つ
4. 作った後継状態公理と (16.5)–(16.24) の同値性 (どの式が Poss と状態制約を要するか)
5. 基本行動理論と、p.665 の例 [stack(A, B), pickup(C), putdown(C)] の実行可能性・射影
   (回帰による判定と、一階の帰結としての直接の判定)
6. 本書 p.662 の Executable の定義はそのままだと矛盾すること
7. プランニング (§16.4): Sussman の異常 (Sussman anomaly)
"""

from collections.abc import Sequence

from z3 import And, Exists, Implies, Not, Or

from sc.sitcalc.axioms import (
    ActionPreconditionAxiom,
    InitialFluentDefinition,
    Sentence,
    closed_initial_database,
    forall,
)
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
from sc.sitcalc.regression import (
    entailed_by_initial_database,
    executability_conditions,
    expand_poss,
    regress,
)
from sc.sitcalc.reiter import EffectAxiom, ReiterDerivation, successor_state_axiom
from sc.sitcalc.solving import Satisfiability, Verdict, entails, satisfiable
from sc.sitcalc.theory import BasicActionTheory
from sc.viz.export import ExampleTrace, StateTrace
from sc.viz.terminal import Report, towers_text
from sc.viz.tree import situation_tree

# ---------------------------------------------------------------------------
# 言語 (p.649–650)
# ---------------------------------------------------------------------------


class Block(DomainObject):
    """ソート block の項."""

    __slots__ = ()


BLOCK = enumeration("Block", ["A", "B", "C"], Block)
A, B, C = BLOCK.constants()

LANG = SitCalcLanguage(
    "blocks",
    actions=[
        Signature("stack", (BLOCK, BLOCK)),  # stack(x, y): 持っている x を y の上に置く
        Signature("unstack", (BLOCK, BLOCK)),  # unstack(x, y): y の上の x を取る
        Signature("pickup", (BLOCK,)),  # pickup(x): 机の上の x を取る
        Signature("putdown", (BLOCK,)),  # putdown(x): 持っている x を机に置く
    ],
    fluents=[
        Signature("on", (BLOCK, BLOCK)),  # on(x, y): x が y の上にある
        Signature("ontable", (BLOCK,)),  # ontable(x): x が机の上にある
        Signature("clear", (BLOCK,)),  # clear(x): x の上に何もなく、手にも持っていない
        Signature("holding", (BLOCK,)),  # holding(x): x を持っている
        Signature("handempty"),  # handempty: 手が空
    ],
)


def stack(x: Block, y: Block) -> Action:
    """ブロック x を y の上に積む行動の項.

    Args:
        x: ブロック x。
        y: 積む先のブロック y。

    Returns:
        行動の項。
    """
    return LANG.actions["stack"](x, y)


def unstack(x: Block, y: Block) -> Action:
    """ブロック y の上の x を取る行動の項.

    Args:
        x: ブロック x。
        y: x が載っているブロック y。

    Returns:
        行動の項。
    """
    return LANG.actions["unstack"](x, y)


def pickup(x: Block) -> Action:
    """机の上の x を取る行動の項.

    Args:
        x: ブロック x。

    Returns:
        行動の項。
    """
    return LANG.actions["pickup"](x)


def putdown(x: Block) -> Action:
    """持っている x を机に置く行動の項.

    Args:
        x: ブロック x。

    Returns:
        行動の項。
    """
    return LANG.actions["putdown"](x)


def on(x: Block, y: Block) -> Fluent:
    """「x が y の上にある」というフルエントの項.

    Args:
        x: ブロック x。
        y: ブロック y。

    Returns:
        フルエントの項。
    """
    return LANG.fluents["on"](x, y)


def ontable(x: Block) -> Fluent:
    """「x が机の上にある」というフルエントの項.

    Args:
        x: ブロック x。

    Returns:
        フルエントの項。
    """
    return LANG.fluents["ontable"](x)


def clear(x: Block) -> Fluent:
    """「x の上に何もなく手にも持っていない」というフルエントの項.

    Args:
        x: ブロック x。

    Returns:
        フルエントの項。
    """
    return LANG.fluents["clear"](x)


def holding(x: Block) -> Fluent:
    """「x を持っている」というフルエントの項.

    Args:
        x: ブロック x。

    Returns:
        フルエントの項。
    """
    return LANG.fluents["holding"](x)


def handempty() -> Fluent:
    """「手が空」というフルエントの項.

    Returns:
        フルエントの項。
    """
    return LANG.fluents["handempty"]()


do = LANG.do
holds = LANG.holds
poss = LANG.poss
S0 = LANG.s0

x, y, u, v, w = BLOCK.vars("x", "y", "u", "v", "w")
a = LANG.action_var("a")
s = LANG.situation_var("s")

# ---------------------------------------------------------------------------
# 行動前提条件公理 (16.1)–(16.4)
# ---------------------------------------------------------------------------

D_AP: tuple[ActionPreconditionAxiom, ...] = (
    # (16.1) Poss(stack(x, y), s) ≡ holding(x, s) ∧ clear(y, s)
    ActionPreconditionAxiom(
        language=LANG, action_symbol=LANG.actions["stack"], params=(x, y), situation=s,
        pi=And(holds(holding(x), s), holds(clear(y), s)), ref="(16.1)",
    ),
    # (16.2) Poss(unstack(x, y), s) ≡ on(x, y, s) ∧ clear(x, s) ∧ handempty(s)
    ActionPreconditionAxiom(
        language=LANG, action_symbol=LANG.actions["unstack"], params=(x, y), situation=s,
        pi=And(holds(on(x, y), s), holds(clear(x), s), holds(handempty(), s)), ref="(16.2)",
    ),
    # (16.3) Poss(pickup(x), s) ≡ ontable(x, s) ∧ clear(x, s) ∧ handempty(s)
    ActionPreconditionAxiom(
        language=LANG, action_symbol=LANG.actions["pickup"], params=(x,), situation=s,
        pi=And(holds(ontable(x), s), holds(clear(x), s), holds(handempty(), s)), ref="(16.3)",
    ),
    # (16.4) Poss(putdown(x), s) ≡ holding(x, s)
    ActionPreconditionAxiom(
        language=LANG, action_symbol=LANG.actions["putdown"], params=(x,), situation=s,
        pi=holds(holding(x), s), ref="(16.4)",
    ),
)  # fmt: skip

# ---------------------------------------------------------------------------
# 効果の完全な仕様 (16.5)–(16.24): 行動ごとに、各フルエントの値を完全に定める
# ---------------------------------------------------------------------------


class ActionSpec:
    """(16.5)–(16.24) の 1 つ: ∀x⃗, s. φ(do(A(x⃗), s)) (自由変数は u, v と行動の引数).

    Attributes:
        ref: 本書の式番号。
        action: 行動の項 A(x⃗) (Poss の前提に使う)。
        variables: 自由変数 (s 以外)。
        body: 式の本体 φ(do(A(x⃗), s)) (自由変数を含む)。
    """

    def __init__(self, ref: str, action: Action, variables: Sequence[Block], body: Formula) -> None:
        """式を登録する.

        Args:
            ref: 本書の式番号。
            action: 行動の項 A(x⃗)。
            variables: 自由変数 (s 以外)。
            body: 式の本体。
        """
        self.ref = ref
        self.action = action
        self.variables = tuple(variables)
        self.body = body

    @property
    def sentence(self) -> Sentence:
        """全称閉包."""
        return Sentence(
            ref=self.ref, sentence=forall([*self.variables, s], self.body), display=show(self.body)
        )


def _spec(ref: str, action: Action, variables: Sequence[Block], body: Formula) -> ActionSpec:
    """(16.5)–(16.24) の 1 つを作る (表を短く書くための略記).

    Args:
        ref: 本書の式番号。
        action: 行動の項。
        variables: 自由変数 (s 以外)。
        body: 式の本体。

    Returns:
        式。
    """
    return ActionSpec(ref, action, variables, body)


_st, _un, _pu, _pd = do(stack(x, y), s), do(unstack(x, y), s), do(pickup(x), s), do(putdown(x), s)

ACTION_SPECS: tuple[ActionSpec, ...] = (
    # stack(x, y)
    _spec("(16.5)", stack(x, y), (u, x, y),
          holds(holding(u), _st) == And(holds(holding(u), s), ne(u, x))),
    _spec("(16.6)", stack(x, y), (x, y), holds(handempty(), _st)),
    _spec("(16.7)", stack(x, y), (u, v, x, y),
          holds(on(u, v), _st) == Or(And(eq(u, x), eq(v, y)), holds(on(u, v), s))),
    _spec("(16.8)", stack(x, y), (u, x, y),
          holds(clear(u), _st) == Or(eq(u, x), And(holds(clear(u), s), ne(u, y)))),
    _spec("(16.9)", stack(x, y), (u, x, y), holds(ontable(u), _st) == holds(ontable(u), s)),
    # unstack(x, y)
    _spec("(16.10)", unstack(x, y), (u, x, y), holds(holding(u), _un) == eq(u, x)),
    _spec("(16.11)", unstack(x, y), (x, y), Not(holds(handempty(), _un))),
    _spec("(16.12)", unstack(x, y), (u, v, x, y),
          holds(on(u, v), _un) == And(holds(on(u, v), s), Not(And(eq(x, u), eq(y, v))))),
    _spec("(16.13)", unstack(x, y), (u, x, y),
          holds(clear(u), _un) == Or(eq(u, y), And(holds(clear(u), s), ne(u, x)))),
    _spec("(16.14)", unstack(x, y), (u, x, y), holds(ontable(u), _un) == holds(ontable(u), s)),
    # pickup(x)
    _spec("(16.15)", pickup(x), (u, x), holds(holding(u), _pu) == eq(u, x)),
    _spec("(16.16)", pickup(x), (x,), Not(holds(handempty(), _pu))),
    _spec("(16.17)", pickup(x), (u, v, x), holds(on(u, v), _pu) == holds(on(u, v), s)),
    _spec("(16.18)", pickup(x), (u, x), holds(clear(u), _pu) == And(holds(clear(u), s), ne(u, x))),
    _spec("(16.19)", pickup(x), (u, x),
          holds(ontable(u), _pu) == And(holds(ontable(u), s), ne(x, u))),
    # putdown(x)
    _spec("(16.20)", putdown(x), (u, x),
          holds(holding(u), _pd) == And(holds(holding(u), s), ne(u, x))),
    _spec("(16.21)", putdown(x), (x,), holds(handempty(), _pd)),
    _spec("(16.22)", putdown(x), (u, v, x), holds(on(u, v), _pd) == holds(on(u, v), s)),
    _spec("(16.23)", putdown(x), (u, x), holds(clear(u), _pd) == Or(eq(u, x), holds(clear(u), s))),
    _spec("(16.24)", putdown(x), (u, x),
          holds(ontable(u), _pd) == Or(eq(u, x), holds(ontable(u), s))),
)  # fmt: skip

# ---------------------------------------------------------------------------
# 効果公理 (16.32)–(16.49)
# ---------------------------------------------------------------------------


def _eff(
    ref: str, fluent: Fluent, action: Action, variables: Sequence[Block], *, positive: bool
) -> EffectAxiom:
    """効果公理 (16.32)–(16.49) の 1 つを作る (表を短く書くための略記).

    Args:
        ref: 本書の式番号。
        fluent: フルエントの項 F(t⃗)。
        action: 行動の項 A(r⃗)。
        variables: 自由変数 (s 以外)。
        positive: F を真にするなら True、偽にするなら False。

    Returns:
        効果公理 (条件なし)。
    """
    return EffectAxiom(
        language=LANG, positive=positive, fluent=fluent, action=action, situation=s,
        variables=tuple(variables), ref=ref,
    )  # fmt: skip


EFFECT_AXIOMS: tuple[EffectAxiom, ...] = (
    _eff("(16.32)", on(x, y), stack(x, y), (x, y), positive=True),
    _eff("(16.33)", clear(x), stack(x, y), (x, y), positive=True),
    _eff("(16.34)", clear(y), stack(x, y), (x, y), positive=False),
    _eff("(16.35)", handempty(), stack(x, y), (x, y), positive=True),
    _eff("(16.36)", holding(x), stack(x, y), (x, y), positive=False),
    _eff("(16.37)", on(x, y), unstack(x, y), (x, y), positive=False),
    _eff("(16.38)", clear(x), unstack(x, y), (x, y), positive=False),
    _eff("(16.39)", clear(y), unstack(x, y), (x, y), positive=True),
    _eff("(16.40)", handempty(), unstack(x, y), (x, y), positive=False),
    _eff("(16.41)", holding(x), unstack(x, y), (x, y), positive=True),
    _eff("(16.42)", ontable(x), putdown(x), (x,), positive=True),
    _eff("(16.43)", clear(x), putdown(x), (x,), positive=True),
    _eff("(16.44)", handempty(), putdown(x), (x,), positive=True),
    _eff("(16.45)", holding(x), putdown(x), (x,), positive=False),
    _eff("(16.46)", ontable(x), pickup(x), (x,), positive=False),
    _eff("(16.47)", clear(x), pickup(x), (x,), positive=False),
    _eff("(16.48)", handempty(), pickup(x), (x,), positive=False),
    _eff("(16.49)", holding(x), pickup(x), (x,), positive=True),
)


def derive_successor_state_axioms() -> tuple[ReiterDerivation, ...]:
    """効果公理 (16.32)–(16.49) から各フルエントの後継状態公理 (16.50) を作る.

    Returns:
        フルエント記号ごとの導出結果 (言語の宣言順)。
    """
    params: dict[str, tuple[Block, ...]] = {
        "on": (u, v), "ontable": (u,), "clear": (u,), "holding": (u,), "handempty": (),
    }  # fmt: skip
    return tuple(
        successor_state_axiom(
            LANG, sym, EFFECT_AXIOMS, params=params[name], action=a, situation=s, ref="(16.50)"
        )
        for name, sym in LANG.fluents.items()
    )


def book_clear_ssa() -> Formula:
    """p.656 の clear の後継状態公理 (本書の "putdon" は putdown の誤植).

    Returns:
        全称閉包した文。
    """
    return forall(
        [x, a, s],
        holds(clear(x), do(a, s))
        == Or(
            Exists([y.expr], eq(a, stack(x, y))),
            Exists([y.expr], eq(a, unstack(y, x))),
            eq(a, putdown(x)),
            And(
                holds(clear(x), s),
                Not(
                    Or(
                        Exists([y.expr], eq(a, stack(y, x))),
                        Exists([y.expr], eq(a, unstack(x, y))),
                        eq(a, pickup(x)),
                    )
                ),
            ),
        ),
    )


# ---------------------------------------------------------------------------
# 状態制約
# ---------------------------------------------------------------------------


def state_constraints(sit: Situation) -> tuple[tuple[str, str, Formula], ...]:
    """ブロック世界の状態制約 (出典, 表示, 式).

    - p.657 の 4 つ: ブロックはちょうど 1 か所 (手の中・机の上・他のブロックの上) にある
    - p.650 のフルエントの説明から: clear と handempty の意味
    - p.649 の「片手のロボット」から: 持てるブロックは高々 1 つ
    - p.650 の行動の説明 (clear なブロックだけを持ち上げる) から: 持っているブロックの上には何もない
    - p.649 の「塔」から: ブロックの上・下にあるブロックは高々 1 つ

    Args:
        sit: 状況の項。

    Returns:
        (出典, 表示用の文字列, 論理式) の組のタプル。
    """
    on_some = Exists([y.expr], holds(on(x, y), sit))
    return (
        ("p.657", "holding(x, s) ∨ ontable(x, s) ∨ ∃y.on(x, y, s)",
         forall([x], Or(holds(holding(x), sit), holds(ontable(x), sit), on_some))),
        ("p.657", "holding(x, s) ⊃ ¬(ontable(x, s) ∨ ∃y.on(x, y, s))",
         forall([x], Implies(holds(holding(x), sit), Not(Or(holds(ontable(x), sit), on_some))))),
        ("p.657", "ontable(x, s) ⊃ ¬(holding(x, s) ∨ ∃y.on(x, y, s))",
         forall([x], Implies(holds(ontable(x), sit), Not(Or(holds(holding(x), sit), on_some))))),
        ("p.657", "(∃y.on(x, y, s)) ⊃ ¬(holding(x, s) ∨ ontable(x, s))",
         forall([x], Implies(on_some, Not(Or(holds(holding(x), sit), holds(ontable(x), sit)))))),
        ("p.650 (clear の説明)", "clear(x, s) ≡ ¬holding(x, s) ∧ ¬∃y.on(y, x, s)",
         forall([x], holds(clear(x), sit)
                == And(Not(holds(holding(x), sit)), Not(Exists([y.expr], holds(on(y, x), sit)))))),
        ("p.650 (handempty の説明)", "handempty(s) ≡ ¬∃x.holding(x, s)",
         holds(handempty(), sit) == Not(Exists([x.expr], holds(holding(x), sit)))),
        ("p.649 (片手のロボット)", "holding(x, s) ∧ holding(y, s) ⊃ x = y",
         forall([x, y], Implies(And(holds(holding(x), sit), holds(holding(y), sit)), eq(x, y)))),
        ("p.650 (持ち上げるのは clear なブロック)", "holding(x, s) ⊃ ¬∃y.on(y, x, s)",
         forall([x], Implies(holds(holding(x), sit), Not(Exists([y.expr], holds(on(y, x), sit)))))),
        ("p.649 (塔)", "on(x, y, s) ∧ on(x, z, s) ⊃ y = z",
         forall([x, y, w], Implies(And(holds(on(x, y), sit), holds(on(x, w), sit)), eq(y, w)))),
        ("p.649 (塔)", "on(y, x, s) ∧ on(z, x, s) ⊃ y = z",
         forall([x, y, w], Implies(And(holds(on(y, x), sit), holds(on(w, x), sit)), eq(y, w)))),
    )  # fmt: skip


def constraints(sit: Situation) -> Formula:
    """状態制約の連言 C(s) を作る.

    Args:
        sit: 状況の項。

    Returns:
        論理式。
    """
    return And(*(phi for _, _, phi in state_constraints(sit)))


# ---------------------------------------------------------------------------
# 基本行動理論
# ---------------------------------------------------------------------------


def basic_action_theory(
    name: str, initial: Sequence[InitialFluentDefinition] = ()
) -> BasicActionTheory:
    """Reiter の手続きで作った後継状態公理を使う基本行動理論.

    Args:
        name: 理論の名前 (表示用)。
        initial: D_S0 (省略すると空)。

    Returns:
        基本行動理論。
    """
    return BasicActionTheory(
        name=name,
        language=LANG,
        d_ss=[d.ssa for d in derive_successor_state_axioms()],
        d_ap=D_AP,
        d_s0=initial,
    )


# p.665 の例のための初期状況 (本書には D_S0 の記述がないので、例が実行可能になるよう選んだ)
PROJECTION_INITIAL = closed_initial_database(
    LANG,
    [holding(A), ontable(B), clear(B), ontable(C), clear(C)],
    ref="—",
    note="本書の p.665 の例には D_S0 がないので、A を持ち B, C が机の上にある状況とした (閉世界)",
)

# Sussman の異常: C が A の上、B は机の上。ゴールは on(A, B) ∧ on(B, C)
SUSSMAN_INITIAL = closed_initial_database(
    LANG,
    [on(C, A), ontable(A), ontable(B), clear(C), clear(B), handempty()],
    ref="—",
    note="Sussman の異常: C が A の上、B は机の上 (閉世界)",
)


def sussman_goal(sit: Situation) -> Formula:
    """ゴール on(A, B) ∧ on(B, C) を作る.

    Args:
        sit: 状況の項。

    Returns:
        論理式。
    """
    return And(holds(on(A, B), sit), holds(on(B, C), sit))


# ---------------------------------------------------------------------------
# 可視化用
# ---------------------------------------------------------------------------


def state_trace(state: frozenset[Fluent]) -> StateTrace:
    """真なフルエントの集合から、塔の形を作る.

    Args:
        state: 真な基礎的なフルエントの集合。

    Returns:
        ビューア用の状態 (下から上への塔、持っているブロック、真なフルエント)。
    """
    blocks = BLOCK.constants()
    above: dict[str, str] = {}
    for b1 in blocks:
        for b2 in blocks:
            if on(b1, b2) in state:
                above[str(b2)] = str(b1)
    towers: list[list[str]] = []
    for b in blocks:
        if ontable(b) in state:
            tower = [str(b)]
            while tower[-1] in above:
                tower.append(above[tower[-1]])
            towers.append(tower)
    held = [str(b) for b in blocks if holding(b) in state]
    return {
        "towers": towers,
        "holding": held[0] if held else None,
        "fluents": sorted(show(f.expr) for f in state),
    }


# ---------------------------------------------------------------------------
# 実行
# ---------------------------------------------------------------------------


def run() -> ExampleTrace:  # noqa: C901, PLR0915
    """例題を実行する.

    Returns:
        この例題の記録 (ビューア用。検査結果を含む)。

    Raises:
        CheckFailedError: 期待と違う検査があったとき (記録は例外の ``trace`` に入る)。
    """
    r = Report("blocks_world", "例 2: ブロック世界", "§16.1, §16.2.1, §16.3, §16.4")

    # 1 -----------------------------------------------------------------------
    r.section("1. 言語と効果の完全な仕様", "p.649–652, (16.1)–(16.24)")
    r.text("ソート: block = {A, B, C}。行動: stack(x, y), unstack(x, y), pickup(x), putdown(x)。")
    r.text("関係フルエント: on(x, y), ontable(x), clear(x), holding(x), handempty。")
    r.axiom_list("行動前提条件公理", "(16.1)–(16.4)", D_AP)
    r.axiom_list(
        "効果の完全な仕様 (行動ごと)",
        "(16.5)–(16.24)",
        [spec.sentence for spec in ACTION_SPECS],
        note="自由変数は全称量化されている (p.651)",
    )

    # 2 -----------------------------------------------------------------------
    r.section("2. Reiter の手続き: 効果公理から後継状態公理へ", "§16.2.1, (16.32)–(16.50)")
    r.axiom_list("効果公理", "(16.32)–(16.49)", EFFECT_AXIOMS)
    derivations = derive_successor_state_axioms()
    for d in derivations:
        for eff, gamma in (*d.positive, *d.negative):
            sign = "" if eff.positive else "¬"
            args = "u⃗, " if d.fluent.arity else ""
            r.formula(
                f"{eff.ref} → γ(a, {args}s) ⊃ {sign}{d.fluent.name}({args}do(a, s)) の γ",
                gamma,
                "p.655",
            )
        r.formula(f"{d.fluent.name} の後継状態公理", d.ssa.statement(), "(16.50)")
    clear_ssa = next(d.ssa for d in derivations if d.fluent.name == "clear")
    r.expect_entailment(
        "作った clear の後継状態公理は p.656 のものと同値",
        entails([], clear_ssa.formula == book_clear_ssa()),
        Verdict.ENTAILED,
        ref="p.656",
        detail="本書 p.656 の 'a = putdon(x)' は putdown(x) の誤植として扱った",
    )

    # 3 -----------------------------------------------------------------------
    r.section("3. 整合性の仮定 ¬(γ⁺ ∧ γ⁻)", "p.656")
    generic = basic_action_theory("ブロック世界 (D_S0 なし)")
    for d in derivations:
        unconditional = entails([], d.consistency)
        expected = Verdict.NOT_ENTAILED if d.fluent.name == "clear" else Verdict.ENTAILED
        detail = ""
        if unconditional.countermodel is not None:
            m = unconditional.countermodel
            witness = m.eval(a.expr, model_completion=True)
            detail = f"反例: a = {witness} (γ⁺ と γ⁻ の両方が成り立つ)"
        r.expect_entailment(
            f"{d.fluent.name}: 無条件に ¬(γ⁺ ∧ γ⁻)",
            unconditional,
            expected,
            ref="p.656",
            detail=detail,
        )
        if d.fluent.name == "clear":
            params = d.ssa.params
            conditional = forall(
                [*params, a, s],
                Implies(And(poss(a, s), constraints(s)), Not(And(d.gamma_plus, d.gamma_minus))),
            )
            r.expect_entailment(
                "clear: Poss(a, s) と状態制約のもとでは ¬(γ⁺ ∧ γ⁻)",
                generic.entails(conditional),
                Verdict.ENTAILED,
                ref="p.656",
                detail=(
                    "stack(u, u) には holding(u) ∧ clear(u) が要るが、"
                    "clear の意味 (p.650) と矛盾する"
                ),
            )

    # 4 -----------------------------------------------------------------------
    r.section("4. 後継状態公理と (16.5)–(16.24) の同値性", "p.652, p.656")
    r.axiom_list(
        "状態制約",
        "p.649–650, p.657",
        [Sentence(ref=ref, sentence=phi, display=text) for ref, text, phi in state_constraints(s)],
        note="p.657 の 4 つ以外は、本書のフルエントの説明 (p.649–650) を式にしたもの",
    )
    rows: list[list[str]] = []
    needs_condition: list[str] = []
    for spec in ACTION_SPECS:
        plain = generic.entails(spec.sentence.formula, timeout_ms=5_000)
        cond_result = "—"
        if not plain.entailed:
            conditional = forall(
                [*spec.variables, s],
                Implies(And(poss(spec.action, s), constraints(s)), spec.body),
            )
            res = generic.entails(conditional)
            cond_result = res.verdict.value
            if res.entailed:
                needs_condition.append(spec.ref)
        rows.append([spec.ref, show(spec.body), plain.verdict.value, cond_result])
    r.table(
        "D_ss ∪ D_ap ⊨ (16.5)–(16.24) ?",
        ["式", "内容", "無条件", "Poss(A(x⃗), s) ∧ 状態制約 のもとで"],
        rows,
    )
    r.text(
        "「無条件」が unknown の式は、量化子を含む理論の反例モデルを Z3 が作れなかったもの。"
        "状態制約に反する初期状況 (A と B を同時に持っている) を与えると、具体的な反例が得られる:"
    )
    odd = basic_action_theory(
        "ブロック世界 (状態制約に反する初期状況)",
        closed_initial_database(LANG, [holding(A), holding(B), ontable(C), clear(C)], ref="—"),
    )
    r.expect_entailment(
        "D ∪ {holding(A, S0), holding(B, S0), …} ⊨ ¬(16.10) の例 (u = B, x = A, y = C, s = S0)",
        odd.entails(Not(holds(holding(B), do(unstack(A, C), S0)) == eq(B, A))),
        Verdict.ENTAILED,
        ref="(16.10)",
        detail=(
            "後継状態公理では holding(B) は unstack(A, C) の後も保たれる (u = x ∨ holding(u, s))"
        ),
    )
    r.expect_entailment(
        "D ∪ {holding(A, S0), holding(B, S0), …} ⊨ ¬(16.15) の例 (u = B, x = C, s = S0)",
        odd.entails(Not(holds(holding(B), do(pickup(C), S0)) == eq(B, C))),
        Verdict.ENTAILED,
        ref="(16.15)",
    )
    r.expect(
        "Poss と状態制約が必要な式",
        ok=needs_condition == ["(16.10)", "(16.15)"],
        actual=", ".join(needs_condition) or "(なし)",
        expected="(16.10), (16.15)",
        ref="(16.10), (16.15)",
        detail=(
            "(16.10) holding(u, do(unstack(x, y), s)) ≡ u = x は、s で他のブロック u を持っていない"
            "ことを前提にしている。Reiter の後継状態公理からは u = x ∨ holding(u, s) しか出ない。"
            "Poss (handempty) と handempty の意味から holding(u, s) が偽になる。(16.15) も同様"
        ),
    )

    # 5 -----------------------------------------------------------------------
    r.section("5. 基本行動理論と、行動列の実行可能性・射影", "§16.3, p.664–665")
    bat = basic_action_theory("ブロック世界 (p.665 の例)", PROJECTION_INITIAL)
    r.theory(bat)
    r.expect_sat(
        "定理 16.1: D_una ∪ D_S0 は充足可能",
        bat.relative_satisfiability(),
        Satisfiability.SAT,
        ref="Theorem 16.1",
    )
    r.expect_entailment("D ⊨ 状態制約(S0)", bat.entails(constraints(S0)), Verdict.ENTAILED)

    sequence = [stack(A, B), pickup(C), putdown(C)]
    r.text("p.665: 行動列 [stack(A, B), pickup(C), putdown(C)] は S0 で実行可能か。")
    conds = executability_conditions(bat, sequence)
    for i, cond in enumerate(conds, start=1):
        r.formula(f"手順 1 ({i})", cond, "p.665")
        expanded = expand_poss(bat, cond)
        r.formula(f"手順 2 ({i}): 行動前提条件公理で書き換え", expanded, "p.665")
        reg = regress(bat, expanded)
        r.formula(f"手順 3 ({i}): 回帰の結果 (S0 で uniform)", reg.result, "p.665")
        r.expect_entailment(
            f"D_una ∪ D_S0 ⊨ 回帰の結果 ({i})",
            entailed_by_initial_database(bat, reg.result),
            Verdict.ENTAILED,
            ref="p.665",
        )
    r.expect_entailment(
        "直接: D ⊨ Poss(stack(A, B), S0) ∧ Poss(pickup(C), …) ∧ Poss(putdown(C), …)",
        bat.entails(And(*conds)),
        Verdict.ENTAILED,
        ref="p.665",
    )
    final = LANG.do_sequence(sequence)
    projection = And(
        holds(on(A, B), final), holds(ontable(C), final), holds(clear(C), final),
        holds(clear(A), final), Not(holds(clear(B), final)), holds(handempty(), final),
    )  # fmt: skip
    r.formula("射影 (temporal projection) の問い", projection, "p.664")
    reg = regress(bat, projection)
    r.formula("回帰の結果", reg.result, "p.664")
    r.expect_entailment(
        "D_una ∪ D_S0 ⊨ 回帰の結果",
        entailed_by_initial_database(bat, reg.result),
        Verdict.ENTAILED,
        ref="p.664",
    )
    r.expect_entailment(
        "直接: D ⊨ 射影の問い", bat.entails(projection), Verdict.ENTAILED, ref="p.664"
    )

    bad = [pickup(C), pickup(B)]
    bad_conds = And(*executability_conditions(bat, bad))
    r.expect_entailment(
        "実行できない例: D ⊨ [pickup(C), pickup(B)] が実行可能 ?",
        entailed_by_initial_database(bat, regress(bat, bad_conds).result),
        Verdict.NOT_ENTAILED,
        ref="p.665",
    )
    r.expect_entailment(
        "実行できない例: D ⊨ ¬([pickup(C), pickup(B)] が実行可能)",
        entailed_by_initial_database(bat, regress(bat, Not(bad_conds)).result),
        Verdict.ENTAILED,
        ref="p.665",
        detail="A を持っているので handempty(S0) が偽",
    )

    # 6 -----------------------------------------------------------------------
    r.section("6. 本書 p.662 の Executable の定義について", "p.662")
    book_exec = bat.book_executable_definition()
    r.formula("本書の定義 (1)", book_exec[0], "p.662")
    r.formula("本書の定義 (2)", book_exec[1], "p.662")
    others = [ax.formula for g in bat.groups() if g.symbol != "Exec" for ax in g.axioms]
    # 矛盾を導く具体例: s := do(putdown(B), S0), a := putdown(B), s' := S0
    witness = do(putdown(B), S0)
    hint = [
        LANG.executable(witness, witness),
        LANG.executable(witness, do(putdown(B), S0))
        == And(poss(putdown(B), S0), LANG.executable(witness, S0)),
    ]
    r.expect_sat(
        "D (Executable 以外) ∪ 本書の定義 は充足可能か",
        satisfiable([*others, *book_exec, *hint]),
        Satisfiability.UNSAT,
        ref="p.662",
        detail=(
            "(2) に s = do(putdown(B), S0), a = putdown(B), s' = S0 を代入すると、"
            "左辺は (1) より真、右辺は ¬Poss(putdown(B), S0) (B を持っていない) より偽。"
            "Z3 にはこの代入例をヒントとして渡した"
            " (代入例は (1), (2) から従うので、充足可能性は変わらない)"
        ),
    )
    r.text(
        "この実装の BasicActionTheory は、(2) に前提 s ⊏ do(a, s') を補った定義を使う。"
        "これは s ⊑ s' の上の整礎な再帰による定義なので、定義による拡張になっており矛盾を生まない"
        " (公理のままの理論の充足可能性は、量化子のため Z3 では判定できない)。"
    )

    # 7 -----------------------------------------------------------------------
    r.section("7. プランニング: Sussman の異常", "§16.4, p.662, p.666")
    planning_bat = basic_action_theory("ブロック世界 (Sussman の異常)", SUSSMAN_INITIAL)
    r.axiom_list("D_S0", "—", planning_bat.d_s0)
    r.formula("ゴール", sussman_goal(LANG.situation_var("s")), "p.666")
    compiled = planning_bat.compile()
    evaluator = compiled.evaluator()
    r.text("初期状況:\n" + towers_text(state_trace(evaluator.state(S0))))
    result = find_plan(compiled, sussman_goal, max_length=8)
    r.table(
        "反復深化 (長さ n で Executable(S0, do([α1..αn], S0)) ∧ G(do([α1..αn], S0)) を解く)",
        ["n", "結果", "秒"],
        [[str(at.length), at.status, f"{at.seconds:.2f}"] for at in result.attempts],
    )
    plan = result.plan
    r.expect(
        "最短プランの長さ",
        ok=plan is not None and len(plan) == 6,  # noqa: PLR2004
        actual="見つからない" if plan is None else f"{len(plan)} 手: [{', '.join(map(str, plan))}]",
        expected="6 手",
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
            planning_bat.entails(
                And(LANG.executable(S0, plan_situation), sussman_goal(plan_situation))
            ),
            Verdict.ENTAILED,
            ref="p.662",
        )
        r.situation_tree(
            {
                "kind": "situation_tree",
                "title": "Sussman の異常: 状況の木とプラン",
                "goal": "on(A, B) ∧ on(B, C)",
                "plan": [str(act) for act in plan],
                "nodes": situation_tree(evaluator, plan, sussman_goal, state_trace, depth=3),
            }
        )
    return r.finish()


def main() -> None:
    """コマンドラインから実行する."""
    run()


if __name__ == "__main__":
    main()
