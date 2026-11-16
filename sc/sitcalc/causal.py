"""ラミフィケーション問題に対する Lin の解: 因果理論 (§16.2.2, p.657–660)

状態制約 (例: (16.51) up(L1, s) ∧ up(L2, s) ⊃ open(s)) だけでは，行動の間接的な効果が
一意に決まらない．Lin は三項述語 Caused(p, v, s) (「フルエント p が状況 s で真理値 v を
持つように引き起こされる」) を導入した:

- (16.52) Caused(p, true, s) ⊃ Holds(p, s)
- (16.53) Caused(p, false, s) ⊃ ¬Holds(p, s)
- (16.54) true ≠ false ∧ (∀v)(v = true ∨ v = false)
- 因果規則 (causal rule): 直接効果 (16.55)–(16.56) (動的) や (16.57) (静的)
- (16.58) 一般フレーム公理: ¬(∃v)Caused(p, v, do(a, s)) ⊃ [Holds(p, do(a, s)) ≡ Holds(p, s)]
- Caused を最小化 (サーカムスクリプション)．この形の公理では Clark の補完と一致し
  因果公理 (causation axioms) (16.59)–(16.60) が得られる (p.659)

この実装では，因果規則から Clark の補完を機械的に作る (:func:`completion`)
本書 p.661 の注意どおり，Poss は前提に含めない形 (Reiter の本の流儀) にする
"""

from collections.abc import Sequence
from dataclasses import dataclass

import z3

from sc.sitcalc.axioms import Axiom, InitialAxiom, Sentence, forall, instantiate
from sc.sitcalc.language import (
    DomainObject,
    Fluent,
    FluentSymbol,
    Formula,
    ObjectSort,
    SitCalcLanguage,
    Situation,
    Term,
    as_datatype_term,
    as_formula,
    enumeration,
    eq,
    is_variable,
    ne,
)
from sc.sitcalc.pretty import show
from sc.sitcalc.solving import DEFAULT_TIMEOUT_MS, Entailment, entails


class TruthValue(DomainObject):
    """ソート truthValues の項 (true, false) (p.658)"""

    __slots__ = ()


class CausalVocabulary:
    """Caused と真理値のソート (言語の拡張)

    Attributes:
        language: 元の言語
        truth: ソート truthValues (列挙型 {true, false})
        true: 真理値 true
        false: 真理値 false
        caused_decl: ``Caused : Fluent × TruthValue × Situation → Bool`` (未解釈関数)
    """

    def __init__(self, language: SitCalcLanguage) -> None:
        """言語に Caused(p, v, s) と真理値のソートを加える

        Args:
            language: 元の言語
        """
        self.language = language
        # (16.54) は列挙型の意味論 (2 つの値は異なり，値はこれで全部) で自動的に成り立つ
        self.truth: ObjectSort[TruthValue] = enumeration(
            f"TruthValue_{language.domain}", ["true", "false"], TruthValue
        )
        self.true, self.false = self.truth.constants()
        self.caused_decl = z3.Function(
            "Caused", language.fluent_sort, self.truth.sort, language.situation_sort, z3.BoolSort()
        )

    def caused(self, p: Fluent, v: TruthValue, s: Situation) -> Formula:
        """``Caused(p, v, s)`` を作る

        Args:
            p: フルエントの項
            v: 真理値
            s: 状況の項

        Returns:
            論理式
        """
        return as_formula(self.caused_decl(p.expr, v.expr, s.expr))

    def basic_axioms(self) -> tuple[Sentence, ...]:
        """Caused の基本公理 (16.52)–(16.54) を返す

        Returns:
            3 つの文
        """
        lang = self.language
        p = lang.fluent_var("p")
        s = lang.situation_var("s")
        v = self.truth.var("v")
        return (
            Sentence(
                ref="(16.52)",
                sentence=forall([p, s], z3.Implies(self.caused(p, self.true, s), lang.holds(p, s))),
                display="Caused(p, true, s) ⊃ Holds(p, s)",
            ),
            Sentence(
                ref="(16.53)",
                sentence=forall(
                    [p, s], z3.Implies(self.caused(p, self.false, s), z3.Not(lang.holds(p, s)))
                ),
                display="Caused(p, false, s) ⊃ ¬Holds(p, s)",
            ),
            Sentence(
                ref="(16.54)",
                sentence=z3.And(
                    ne(self.true, self.false),
                    forall([v], z3.Or(eq(v, self.true), eq(v, self.false))),
                ),
                display="true ≠ false ∧ (∀v)(v = true ∨ v = false)",
                note="真理値のソートを列挙型にしたので自動的に成り立つ",
            ),
        )

    def frame_axiom(self) -> Sentence:
        """(16.58): 引き起こされない限り，フルエントの真理値は持続する

        Returns:
            (16.58) の文
        """
        lang = self.language
        p = lang.fluent_var("p")
        a = lang.action_var("a")
        s = lang.situation_var("s")
        v = self.truth.var("v")
        after = lang.do(a, s)
        return Sentence(
            ref="(16.58)",
            sentence=forall(
                [p, a, s],
                z3.Implies(
                    z3.Not(z3.Exists([v.expr], self.caused(p, v, after))),
                    lang.holds(p, after) == lang.holds(p, s),
                ),
            ),
            display="¬(∃v)Caused(p, v, do(a, s)) ⊃ [Holds(p, do(a, s)) ≡ Holds(p, s)]",
        )


@dataclass(frozen=True, eq=False, kw_only=True)
class CausalRule(Axiom):
    """因果規則 ``φ ⊃ Caused(F(t⃗), v, σ)``

    Attributes:
        vocabulary: Caused を含む語彙
        fluent: フルエントの項 F(t⃗) (変数を含んでよい)
        value: 真理値 v
        situation: 状況項 σ (静的な規則では変数 s，動的な規則では do(A(…), s) など)
        condition: 条件 φ
        variables: 自由変数 (状況変数を含む)
        static: 静的な規則 (1 つの状況だけに言及する) か (p.658)

    """

    vocabulary: CausalVocabulary
    fluent: Fluent
    value: TruthValue
    situation: Situation
    condition: Formula
    variables: tuple[Term, ...]
    static: bool

    @property
    def consequent(self) -> Formula:
        """``Caused(F(t⃗), v, σ)``"""
        return self.vocabulary.caused(self.fluent, self.value, self.situation)

    @property
    def formula(self) -> Formula:
        """全称閉包"""
        return forall(self.variables, z3.Implies(self.condition, self.consequent))

    def statement(self) -> str:
        """本書の書き方で表示する

        Returns:
            表示用の文字列
        """
        return f"{show(self.condition)} ⊃ {show(self.consequent, shorthand=False)}"

    def case(self, params: Sequence[DomainObject], v: TruthValue, s: Situation) -> Formula:
        """補完の 1 項: ``∃(残りの変数). u⃗ = t⃗ ∧ v = value ∧ s = σ ∧ φ``

        t_i や σ が (まだ使っていない) 自由変数なら u_i や s に名前を付け替え
        そうでなければ等式を加える (Reiter の手続きの正規化と同じ)．残りの変数は
        補完の自由変数 (u⃗, v, s) と衝突しないよう s' のようにプライムを付けて存在量化する
        規則側の項への置き換えは同時に 1 回だけ行う (変数の捕獲を避けるため)

        Args:
            params: 補完の変数 u⃗ (F の引数)
            v: 補完の変数 v
            s: 補完の変数 s

        Returns:
            補完の右辺の 1 項
        """
        args = [DomainObject(as_datatype_term(c)) for c in self.fluent.expr.children()]
        renamed: list[Term] = []
        renamed_to: list[Term] = []

        def is_free(t: Term) -> bool:
            """規則の自由変数で，まだ付け替えていないものかを判定する

            Args:
                t: 項

            Returns:
                付け替えに使えるなら True
            """
            own = any(t.expr.eq(w.expr) for w in self.variables)
            done = any(t.expr.eq(w.expr) for w in renamed)
            return is_variable(t) and own and not done

        pending_args: list[tuple[DomainObject, DomainObject]] = []
        for t, u in zip(args, params, strict=True):
            if is_free(t):
                renamed.append(t)
                renamed_to.append(u)
            else:
                pending_args.append((u, t))
        sigma_is_var = is_free(self.situation)
        if sigma_is_var:
            renamed.append(self.situation)
            renamed_to.append(s)
        rest = [w for w in self.variables if not any(w.expr.eq(r.expr) for r in renamed)]
        primed = [_primed(w) for w in rest]

        def rule_side(phi: Formula) -> Formula:
            """規則側の論理式の変数を (同時に 1 回だけ) 付け替える

            Args:
                phi: 規則側の論理式

            Returns:
                付け替えた論理式
            """
            return instantiate(phi, [*renamed, *rest], [*renamed_to, *primed])

        def rule_term[T: Term](t: T) -> T:
            """規則側の項の変数を (同時に 1 回だけ) 付け替える

            Args:
                t: 規則側の項

            Returns:
                付け替えた項 (同じクラス)
            """
            replaced = instantiate(eq(t, t), [*renamed, *rest], [*renamed_to, *primed])
            return type(t)(as_datatype_term(replaced.arg(0)))

        parts = [eq(v, self.value)]
        parts += [eq(u, rule_term(t)) for u, t in pending_args]
        if not sigma_is_var:
            parts.append(eq(s, rule_term(self.situation)))
        parts.append(rule_side(self.condition))
        body = z3.And(*parts)
        return z3.Exists([w.expr for w in primed], body) if primed else body


def _primed(t: Term) -> Term:
    """同じソートで名前にプライムを付けた変数 (例: s → s')

    Args:
        t: 変数

    Returns:
        新しい変数 (同じクラス，名前は ``t'``)
    """
    return type(t)(as_datatype_term(z3.Const(f"{t.expr}'", t.expr.sort())))


def completion(vocabulary: CausalVocabulary, rules: Sequence[CausalRule]) -> tuple[Sentence, ...]:
    """Caused の Clark の補完 = 因果公理 (causation axioms) (16.59)–(16.60)

    各フルエント記号 F について:

        ∀x⃗, v, s. Caused(F(x⃗), v, s) ≡ ⋁ (F についての各規則の項)

    フルエントのデータ型は領域閉包を満たすので，記号ごとの補完の連言は Caused 全体の
    補完と同値．規則のない記号 F については ¬Caused(F(x⃗), v, s)

    Args:
        vocabulary: Caused を含む語彙
        rules: 因果規則

    Returns:
        フルエント記号ごとの因果公理
    """
    lang = vocabulary.language
    v = vocabulary.truth.var("v")
    s = lang.situation_var("s")
    result: list[Sentence] = []
    for sym in lang.fluents.values():
        params = _fluent_params(sym)
        mine = [rule for rule in rules if sym.matches(rule.fluent)]
        cases = [rule.case(params, v, s) for rule in mine]
        rhs = (cases[0] if len(cases) == 1 else z3.Or(*cases)) if cases else z3.BoolVal(False)
        lhs = vocabulary.caused(sym(*params), v, s)
        result.append(
            Sentence(
                ref="(16.59)–(16.60)",
                sentence=forall([*params, v, s], lhs == rhs),
                display=f"{show(lhs, shorthand=False)} ≡ {show(rhs)}",
                note="Caused のサーカムスクリプション (= Clark の補完, p.659)",
            )
        )
    return tuple(result)


def _fluent_params(sym: FluentSymbol) -> tuple[DomainObject, ...]:
    """補完に使う，フルエント記号の引数の変数を作る

    Args:
        sym: フルエントの関数記号

    Returns:
        変数のタプル (x, y, z, x4, ...)
    """
    names = ["x", "y", "z"]
    return tuple(
        p.var(names[i] if i < len(names) else f"x{i + 1}") for i, p in enumerate(sym.params)
    )


class CausalTheory:
    """Lin の因果理論 (§16.2.2): 基本公理 + 因果規則の補完 + フレーム公理 (16.58) + D_S0

    Attributes:
        name: 理論の名前 (表示用)
        vocabulary: Caused を含む語彙
        rules: 因果規則
        d_s0: 初期状況の公理
        causation_axioms: 因果規則の Clark の補完 (16.59)–(16.60)
    """

    def __init__(
        self,
        *,
        name: str,
        vocabulary: CausalVocabulary,
        rules: Sequence[CausalRule],
        d_s0: Sequence[InitialAxiom] = (),
    ) -> None:
        """理論を作り，因果規則の補完を計算する

        Args:
            name: 理論の名前 (表示用)
            vocabulary: Caused を含む語彙
            rules: 因果規則
            d_s0: 初期状況の公理
        """
        self.name = name
        self.vocabulary = vocabulary
        self.rules = tuple(rules)
        self.d_s0 = tuple(d_s0)
        self.causation_axioms = completion(vocabulary, rules)

    def groups(self) -> tuple[tuple[str, str, tuple[Axiom, ...]], ...]:
        """理論の構成要素を表示用に返す

        Returns:
            (見出し, 出典, 公理) の組のタプル
        """
        return (
            ("Caused の基本公理", "(16.52)–(16.54)", self.vocabulary.basic_axioms()),
            ("因果規則", "(16.55)–(16.57)", self.rules),
            ("因果公理 (Caused の補完)", "(16.59)–(16.60)", self.causation_axioms),
            ("一般フレーム公理", "(16.58)", (self.vocabulary.frame_axiom(),)),
            ("D_S0", "—", self.d_s0),
        )

    def axioms(self) -> tuple[Formula, ...]:
        """理論の公理を Z3 の式として返す

        因果規則そのものは補完から従うので含めない

        Returns:
            公理のタプル
        """
        return (
            *(ax.formula for ax in self.vocabulary.basic_axioms()),
            *(ax.formula for ax in self.causation_axioms),
            self.vocabulary.frame_axiom().formula,
            *(ax.formula for ax in self.d_s0),
        )

    def entails(self, phi: Formula, *, timeout_ms: int = DEFAULT_TIMEOUT_MS) -> Entailment:
        """``T ⊨ φ`` を判定する

        Args:
            phi: 論理式
            timeout_ms: Z3 の制限時間 (ミリ秒)

        Returns:
            判定結果
        """
        return entails(self.axioms(), phi, timeout_ms=timeout_ms)
