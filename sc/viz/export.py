"""実行結果の JSON 形式 (ビューア ``viz/web/index.html`` が読む).

``run_all`` が各例題の :class:`sc.viz.terminal.Report` を集めて ``out/trace.json`` に書き出す。
"""

import json
from datetime import UTC, datetime
from pathlib import Path
from typing import Literal, TypedDict


class AxiomTrace(TypedDict):
    """公理 1 つ.

    Attributes:
        ref: 本書での出典。
        text: 本書の記法での表示。
        note: 補足説明。
    """

    ref: str
    text: str
    note: str


class AxiomGroupTrace(TypedDict):
    """基本行動理論の構成要素 1 つ (Σ, D_ss, ...).

    Attributes:
        symbol: 本書での記号 (``"D_ss"`` など)。
        title: 日本語名と英語名。
        ref: 本書での出典。
        note: 補足説明。
        axioms: 公理。
    """

    symbol: str
    title: str
    ref: str
    note: str
    axioms: list[AxiomTrace]


class CheckTrace(TypedDict):
    """Z3 による検査 1 つ.

    Attributes:
        label: 何を検査したか。
        ref: 本書での出典。
        expected: 期待した結果。
        actual: 実際の結果。
        ok: 期待どおりか。
        detail: 補足 (反例、Z3 の理由など)。
    """

    label: str
    ref: str
    expected: str
    actual: str
    ok: bool
    detail: str


class TextItem(TypedDict):
    """説明文.

    Attributes:
        kind: ``"text"``。
        text: 本文。
    """

    kind: Literal["text"]
    text: str


class FormulaItem(TypedDict):
    """式の表示.

    Attributes:
        kind: ``"formula"``。
        label: 見出し。
        ref: 本書での出典。
        text: 本書の記法での式。
    """

    kind: Literal["formula"]
    label: str
    ref: str
    text: str


class CheckItem(TypedDict):
    """検査結果.

    Attributes:
        kind: ``"check"``。
        check: 検査結果。
    """

    kind: Literal["check"]
    check: CheckTrace


class TheoryItem(TypedDict):
    """理論 (公理の集まり) の表示.

    Attributes:
        kind: ``"theory"``。
        name: 理論の名前。
        groups: 構成要素。
    """

    kind: Literal["theory"]
    name: str
    groups: list[AxiomGroupTrace]


class TableItem(TypedDict):
    """表 (モデルの列挙など).

    Attributes:
        kind: ``"table"``。
        title: 表題。
        columns: 列の見出し。
        rows: 行 (各セルは文字列)。
    """

    kind: Literal["table"]
    title: str
    columns: list[str]
    rows: list[list[str]]


class StateTrace(TypedDict):
    """ブロック世界の状態.

    Attributes:
        towers: 塔のリスト (各塔は下から上へのブロック名)。
        holding: 持っているブロック (なければ None)。
        fluents: 真なフルエント (本書の記法、整列済み)。
    """

    towers: list[list[str]]
    holding: str | None
    fluents: list[str]


class SituationNodeTrace(TypedDict):
    """状況の木の節点 1 つ.

    Attributes:
        id: 節点の番号。
        parent: 親の節点の番号 (根なら None)。
        action: 親からの行動 (根なら None)。
        term: 状況項 (例: ``do(pickup(B), do(…))``)。
        depth: S0 からの行動の数。
        state: その状況の状態。
        possible: その状況で実行可能な行動。
        on_plan: プランの経路上の状況か。
        goal: その状況でゴールが成り立つか。
    """

    id: int
    parent: int | None
    action: str | None
    term: str
    depth: int
    state: StateTrace
    possible: list[str]
    on_plan: bool
    goal: bool


class SituationTreeItem(TypedDict):
    """状況の木 (S0 を根とし、実行可能な行動で枝分かれする) とプラン.

    Attributes:
        kind: ``"situation_tree"``。
        title: 表題。
        goal: ゴールの表示。
        plan: プラン (行動の表示の列)。
        nodes: 節点。
    """

    kind: Literal["situation_tree"]
    title: str
    goal: str
    plan: list[str]
    nodes: list[SituationNodeTrace]


type ItemTrace = TextItem | FormulaItem | CheckItem | TheoryItem | TableItem | SituationTreeItem


class SectionTrace(TypedDict):
    """例題の中の節.

    Attributes:
        title: 節の見出し。
        ref: 本書での出典。
        items: 節の中身。
    """

    title: str
    ref: str
    items: list[ItemTrace]


class ExampleTrace(TypedDict):
    """例題 1 つ.

    Attributes:
        id: 例題の識別子 (モジュール名)。
        title: 例題の題名。
        ref: 本書での出典。
        sections: 節。
    """

    id: str
    title: str
    ref: str
    sections: list[SectionTrace]


class TraceFile(TypedDict):
    """``out/trace.json`` 全体.

    Attributes:
        generated: 生成日時 (ISO 8601, UTC)。
        source: 出典 (本書)。
        examples: 例題の記録。
    """

    generated: str
    source: str
    examples: list[ExampleTrace]


def write_trace(path: Path, examples: list[ExampleTrace]) -> None:
    """``out/trace.json`` の形式で JSON を書き出す.

    Args:
        path: 書き出し先 (親ディレクトリがなければ作る)。
        examples: 例題の記録。
    """
    data: TraceFile = {
        "generated": datetime.now(UTC).isoformat(timespec="seconds"),
        "source": "F. Lin, Situation Calculus, Handbook of Knowledge Representation, Ch.16 (2008)",
        "examples": examples,
    }
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, ensure_ascii=False, indent=1), encoding="utf-8")
