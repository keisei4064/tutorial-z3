# 状況計算 (Situation Calculus) を Z3 で

F. Lin, “Situation Calculus”, *Handbook of Knowledge Representation*, Ch.16 (2008)
(`Handbook_Ch16_Situation_Calculus.pdf`、git 管理外) の定式化と例題を、Z3 (z3-solver) の
Python API で表現し、解いて、検証する。

## 実行

リポジトリのルートで:

```sh
uv run python -m sc.run_all                    # 全例題を実行・検査し、sc/out/trace.json を書き出す
uv run python -m sc.examples.blocks_world      # 例題を 1 つだけ実行
```

各例題は「本書の主張」を Z3 の判定 (帰結する / しない / 判定不能、sat / unsat) として検査し、
期待と違えば終了コード 1 で終わる (実行がそのままテスト)。現在 6 例題・74 検査がすべて
期待どおりで、全体で約 1 分かかる (うち約 25 秒は「Z3 が判定できない」ことを示すための
意図的なタイムアウト)。

| 例題 | モジュール | 本書 | 内容 |
| --- | --- | --- | --- |
| 例 0 | `examples/regression_toy.py` | §16.3 p.665 | 回帰の定義の小さな例 (F, G) |
| 例 1 | `examples/yale_shooting.py` | §16.2 | Yale Shooting Problem、フレーム問題、Reiter の解 |
| 例 2 | `examples/blocks_world.py` | §16.1, §16.2.1, §16.3, §16.4 | ブロック世界: Reiter の手続き、回帰、射影、Sussman の異常 |
| 例 3 | `examples/blocks_world_move.py` | §16.1 (16.25)–(16.27) | move だけの版 (同じ問題が 3 手で解ける) |
| 例 4 | `examples/suitcase.py` | §16.2.2 | スーツケース: ラミフィケーション、Lin の因果理論 |
| 例 5 | `examples/induction.py` | §16.3 (16.63), p.664 | 帰納法が要る性質と Z3 の限界 |

## 可視化

- **ターミナル** (`viz/terminal.py`): rich で公理・式・検査・表・ブロックの塔 (ASCII) を表示。
- **ビューア** (`viz/web/index.html`): `out/trace.json` を読み、例題ごとに理論 (Σ / D_ss / …)、
  検査結果、状況の木 (S0 を根に実行可能な行動で枝分かれ。プランの経路を 1 手ずつ送れる) を表示する。
  - 手元で見る: `uv run python -m http.server -d sc` を起動して <http://localhost:8000/viz/web/> を開く
    (ファイルを直接開くと fetch できないので、trace.json をページにドラッグ＆ドロップする)。
  - Artifact として公開した版: <https://claude.ai/artifact/MBGZSffc4KKyL7cztLVdJg> (非公開。共有は Share メニューから)。
    `run_all` の後に再公開すると最新の結果になる。

## 検証 (型・lint)

```sh
.venv/bin/pyright sc                                               # strict (ルートの pyproject.toml の [tool.pyright])
.venv/bin/ruff check --config sc/ruff.toml sc                      # select = ["ALL"]
.venv/bin/ruff format --config sc/ruff.toml --check sc
MYPYPATH=sc/typings .venv/bin/stubtest z3 --ignore-missing-stub    # z3 スタブと実装の突き合わせ
.venv/bin/python -m sc.check_docstrings                            # docstring (Google 形式) の検査
```

- docstring は Google 形式 (Args / Returns / Yields / Raises / Attributes)。ruff の D ルールは
  公開 API しか見ないので、`check_docstrings.py` で非公開・ネストした関数・dunder・クラスの
  属性まで検査している。docstring とコメントの句読点 (読点は「，」、文中の句点は「．」、
  行末には句読点を付けない) もこのスクリプトで検査する。
- z3 は `import z3` して `z3.And(...)` のように参照する (`from z3 import ...` は使わない)。

- z3-solver は型情報を同梱していないので、`typings/z3/__init__.pyi` に **sc/ で使う API だけ**
  の部分スタブを書いた。引数名・既定値は mypy の `stubtest` で実装と一致することを確かめている。
- このスタブを全体に効かせると既存ノートブックの型検査が変わるので、ルートの `pyproject.toml` の
  `[tool.pyright]` で `sc/` だけの実行環境 (`executionEnvironments`) を作り、そこでだけスタブを
  優先して読ませている (VS Code の Pylance もこの設定で `sc/` を strict に検査する)。
- ruff で無効にしているのは、日本語の全角文字 (RUF001–003)、式のコメントの誤検出 (ERA001)、
  「。」終わりの docstring (D400/D415) など。理由は `ruff.toml` のコメント参照。

## 構成

```text
sc/
  sitcalc/          ドメインに依存しない本書の理論
    language.py       §16.1   多ソート言語 (Situation / Action / Fluent / ドメインのソート), do, Holds, Poss
    axioms.py         §16.3   公理のクラス (SSA (16.66), 前提条件公理, D_S0), uniform 性 (p.662–663)
    theory.py         §16.3   BasicActionTheory (D = Σ ∪ D_ss ∪ D_ap ∪ D_una ∪ D_S0), 定理 16.1, コンパイル
    reiter.py         §16.2.1 効果公理 → 後継状態公理 (16.50), 整合性の仮定
    causal.py         §16.2.2 Caused, (16.52)–(16.58), 因果規則の Clark 補完 (16.59)–(16.60)
    regression.py     §16.3   回帰
    planning.py       §16.4   有界プランニング (反復深化)
    minimal.py        §16.2   極小モデルの列挙 (有限の原子に制限したサーカムスクリプション)
    simplify.py               同値な量化子の書き換え (構成子の ∃ の消去、有限ソートの展開)
    solving.py                帰結 (D ⊨ φ) と充足可能性の判定
    pretty.py                 本書の記法での表示 (∧ ∨ ¬ ⊃ ≡ ∀ ∃, clear(x, s) の略記)
  examples/         例題 (1 ファイル 1 ドメイン)
  viz/              terminal.py (rich), export.py (JSON の型), tree.py (状況の木), web/index.html
  typings/z3/       z3 の部分スタブ
  run_all.py
```

## 本書との対応

### 用語

| 本書 | コード |
| --- | --- |
| situation / action / fluent (relational) | `Situation` / `Action` / `Fluent` (別々の Python クラス。ソートの取り違えは型エラー) |
| domain sort (block, lock, …) | `DomainObject` のサブクラス + `ObjectSort` (Z3 の列挙型) |
| `S0`, `do(a, s)`, `Holds(p, s)`, `Poss(a, s)` | `lang.s0`, `lang.do(a, s)`, `lang.holds(p, s)`, `lang.poss(a, s)` |
| `do([a1, …, an], s)` (p.662) | `lang.do_sequence([...], s)` |
| `s ⊏ s'`, `s ⊑ s'`, `Executable(s, s')` | `lang.precedes`, `lang.precedes_eq`, `lang.executable` |
| successor state axiom (16.66), Φ_F | `SuccessorStateAxiom(phi=...)` |
| action precondition axiom, Π_A | `ActionPreconditionAxiom(pi=...)` |
| effect axiom, γ⁺ / γ⁻ | `EffectAxiom`, `ReiterDerivation.gamma_plus` / `gamma_minus` |
| basic action theory D = Σ ∪ D_ss ∪ D_ap ∪ D_una ∪ D_S0 | `BasicActionTheory` (`.sigma()`, `.d_ss`, `.d_ap`, `.d_una()`, `.d_s0`) |
| uniform formula | `uniform_violations` (SSA などの作成時に検査) |
| regression | `regress`, `entailed_by_initial_database` |
| relative satisfiability (Theorem 16.1) | `BasicActionTheory.relative_satisfiability` |
| `Caused(p, v, s)`, causal rule, causation axioms | `CausalVocabulary.caused`, `CausalRule`, `completion` |

### Z3 での表し方

- **状況** はデータ型 `Situation = S0 | do(Action, Situation)`。構成子の単射性 (16.62)、
  行動の一意名公理 D_una、「状況は S0 から有限回の do で得られる」(16.63 の帰結) が
  Z3 の意味論で自動的に成り立つ。それでも理論を見えるようにするため、一階の文としても列挙する。
- **関係フルエント** は本書 p.651 にならい一階の対象 (データ型 `Fluent`) とし、`Holds(p, s)` で真偽を表す。
- **自由変数** は本書の慣習 (p.651) どおり全称量化されたものとし、各公理は `formula` で全称閉包を返す。
- **二つの推論の仕方**
  1. `BasicActionTheory.entails(φ)`: D ⊨ φ を一階の帰結として判定 (D ∪ {¬φ} が unsat か)。本書どおりの形。
  2. `BasicActionTheory.compile()`: D_S0 が完全なとき、Holds / Poss / ⊏ / Executable を状況についての
     再帰関数にコンパイルする。プランニングのようにモデルを探す問題は、1 の形だと量化子のせいで
     unknown になりやすい (Sussman の異常で確認) ので、こちらを使う。
- **同値な書き換え** (`simplify.py`)。どちらも一意名と領域閉包のもとで同値。
  - 構成子についての ∃ の消去: `∃x⃗. a = A(x⃗) ∧ φ` → `is_A(a) ∧ φ[x⃗ := 引数(a)]`。
    再帰関数の本体に量化子が残ると探索が止まる (move 版のプランニングで 120 秒 unknown → 0.01 秒 sat)。
  - 列挙型の量化子の展開: `∃y. on(x, y, s)` → `on(x, A, s) ∨ on(x, B, s) ∨ on(x, C, s)`。
- **一点での具体化** (`BasicActionTheory.one_step_instances`): s と do(a, s) にしか言及しない性質は、
  D_ss / D_ap をその 2 点で具体化した量化子のない式から判定できる (D から従う式なので健全)。

## 本書の記述について Z3 で確かめたこと (メモ)

実装中に気づいた点。いずれも例題の中で Z3 に確かめさせている。

1. **(16.28) と Hanks–McDermott** (例 1): (16.28) は「真の持続」しか述べず (式の ⊃ も脱落している)、
   効果公理 (16.29)–(16.30) は abnormal に触れない。この組み合わせでは abnormal が空のモデルが
   唯一の極小モデルで、異常は起きない。p.654 の「2 つのモデル」は、効果公理が「その変化は abnormal」とも
   述べる Hanks–McDermott (McCarthy 1986) の定式化で得られる。
2. **整合性の仮定 ¬(γ⁺ ∧ γ⁻)** (例 2): clear については無条件には成り立たない (`a = unstack(B, B)` が反例)。
   Poss と状態制約のもとでは成り立つ。
3. **(16.5)–(16.24) との同値性** (例 2): Reiter の手続きで作った後継状態公理と同値なのは 18 本で、
   (16.10) と (16.15) だけは Poss と状態制約 (手が空なら他のブロックを持っていない) が要る。
4. **p.656 の clear の後継状態公理**: `putdon` は `putdown` の誤植として扱った (作った SSA と同値)。
5. **p.662 の Executable の定義** (例 2): そのままだと `s = do(a, s')` を代入したときに矛盾する
   (`Executable(s, s)` が真なのに、右辺は ¬Poss で偽)。実装では 2 つ目の式に前提 `s ⊏ do(a, s')` を補った。
6. **(16.25) の move** (例 3): `x ≠ y` がないので `move(B, B)` が実行可能になり、`on(B, B)` が成り立つ。
7. **ブロック世界の状態制約** (例 2, 例 5): p.657 の 4 つと clear / handempty の定義だけでは、
   実行可能な行動で保存されない。「片手」(p.649) と「持っているブロックの上には何もない」(p.650) の
   制約が必要だった (Z3 が反例を返したので追加した)。
8. **例の D_S0**: p.665 の射影の例や Sussman の異常の初期状況は本書にないので補った (コード中に明記)。
