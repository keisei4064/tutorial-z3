"""ターミナル表示 (rich) と、ビューア用データの記録.

各例題は :class:`Report` に節・説明・式・検査結果を書き込む。Report は

- rich でターミナルに表示し、
- 同じ内容を :mod:`sc.viz.export` の形式で記録する (``run_all`` が JSON に書き出す)。

検査 (:meth:`Report.expect` 系) は、期待と違えば記録した上で失敗として数え、
:meth:`Report.finish` で例外を投げる。実行がそのままテストになる。
"""

from collections.abc import Sequence

from rich.console import Console
from rich.markup import escape
from rich.panel import Panel
from rich.rule import Rule
from rich.table import Table
from rich.text import Text

from sc.sitcalc.axioms import Axiom
from sc.sitcalc.language import Formula
from sc.sitcalc.pretty import show
from sc.sitcalc.solving import Entailment, Satisfiability, SatResult, Verdict
from sc.sitcalc.theory import AxiomGroup, BasicActionTheory
from sc.viz.export import (
    AxiomGroupTrace,
    AxiomTrace,
    CheckTrace,
    ExampleTrace,
    ItemTrace,
    SectionTrace,
    StateTrace,
)

console = Console(highlight=False)


class CheckFailedError(AssertionError):
    """期待どおりでない検査があった (記録した結果も持つ).

    Attributes:
        trace: 失敗した例題の記録 (run_all が JSON に書き出すのに使う)。
    """

    def __init__(self, message: str, trace: ExampleTrace) -> None:
        """失敗した検査の名前と、その例題の記録.

        Args:
            message: 期待と違った検査の名前 (カンマ区切り)。
            trace: その例題の記録。
        """
        super().__init__(message)
        self.trace = trace


def group_trace(group: AxiomGroup) -> AxiomGroupTrace:
    """AxiomGroup を JSON 用の形に変換する.

    Args:
        group: 基本行動理論の構成要素。

    Returns:
        JSON 用の辞書 (二階の公理も表示用に含める)。
    """
    axioms = [AxiomTrace(ref=a.ref, text=a.statement(), note=a.note) for a in group.axioms]
    axioms += [AxiomTrace(ref=a.ref, text=a.text, note=a.note) for a in group.second_order]
    return {
        "symbol": group.symbol,
        "title": group.title,
        "ref": group.ref,
        "note": group.note,
        "axioms": axioms,
    }


class Report:
    """1 つの例題の出力 (ターミナル表示と記録).

    Attributes:
        trace: 記録 (ビューア用の JSON の形)。
        failures: 期待と違った検査の名前。
    """

    def __init__(self, example_id: str, title: str, ref: str) -> None:
        """例題の見出しを表示する.

        Args:
            example_id: 例題の識別子 (モジュール名)。
            title: 例題の題名。
            ref: 本書での出典。
        """
        self.trace: ExampleTrace = {"id": example_id, "title": title, "ref": ref, "sections": []}
        self.failures: list[str] = []
        console.print()
        console.print(Panel(Text(f"{title}\n{ref}", style="bold"), border_style="cyan"))

    # -- 構造 ---------------------------------------------------------------

    def section(self, title: str, ref: str = "") -> None:
        """節を始める (以降の内容はこの節に記録する).

        Args:
            title: 節の見出し。
            ref: 本書での出典。
        """
        self.trace["sections"].append({"title": title, "ref": ref, "items": []})
        label = f"{escape(title)}  [dim]{escape(ref)}[/dim]" if ref else escape(title)
        console.print()
        console.print(Rule(label, align="left", style="cyan"))

    def _add(self, item: ItemTrace) -> None:
        """現在の節に内容を記録する (節がなければ無題の節を作る).

        Args:
            item: 記録する内容。
        """
        if not self.trace["sections"]:
            self.section("")
        current: SectionTrace = self.trace["sections"][-1]
        current["items"].append(item)

    # -- 内容 ---------------------------------------------------------------

    def text(self, text: str) -> None:
        """説明文を表示・記録する.

        Args:
            text: 本文。
        """
        self._add({"kind": "text", "text": text})
        console.print(escape(text))

    def formula(self, label: str, phi: Formula | str, ref: str = "") -> None:
        """式を表示・記録する.

        Args:
            label: 見出し。
            phi: 論理式 (本書の記法で表示する) または表示用の文字列。
            ref: 本書での出典。
        """
        text = phi if isinstance(phi, str) else show(phi)
        self._add({"kind": "formula", "label": label, "ref": ref, "text": text})
        head = f"[bold]{escape(label)}[/bold]" + (f" [dim]{escape(ref)}[/dim]" if ref else "")
        console.print(f"{head}\n    {escape(text)}")

    def axioms(self, name: str, groups: Sequence[AxiomGroup]) -> None:
        """公理の集まりを、構成要素ごとに表示・記録する.

        Args:
            name: 理論の名前。
            groups: 構成要素。
        """
        self._add({"kind": "theory", "name": name, "groups": [group_trace(g) for g in groups]})
        console.print(f"[bold]{escape(name)}[/bold]")
        for g in groups:
            table = Table(
                title=escape(f"{g.symbol}: {g.title}  ({g.ref})" if g.title else g.ref),
                title_justify="left",
                show_header=False,
                box=None,
                padding=(0, 1),
            )
            table.add_column("ref", style="dim", no_wrap=True)
            table.add_column("axiom")
            for ax in g.axioms:
                note = f"\n[dim]  ↳ {escape(ax.note)}[/dim]" if ax.note else ""
                table.add_row(escape(ax.ref), escape(ax.statement()) + note)
            for so in g.second_order:
                table.add_row(
                    escape(so.ref), f"{escape(so.text)}\n[dim]  ↳ {escape(so.note)}[/dim]"
                )
            if not g.axioms and not g.second_order:
                table.add_row("", "[dim](なし)[/dim]")
            console.print(table)
            if g.note:
                console.print(f"  [dim]※ {escape(g.note)}[/dim]")

    def theory(self, bat: BasicActionTheory) -> None:
        """基本行動理論 D = Σ ∪ D_ss ∪ D_ap ∪ D_una ∪ D_S0 を表示・記録する.

        Args:
            bat: 基本行動理論。
        """
        self.axioms(f"基本行動理論 D ({bat.name}) = Σ ∪ D_ss ∪ D_ap ∪ D_una ∪ D_S0", bat.groups())

    def axiom_list(self, name: str, ref: str, axioms: Sequence[Axiom], note: str = "") -> None:
        """公理の列を 1 グループとして表示・記録する.

        Args:
            name: 見出し。
            ref: 本書での出典。
            axioms: 公理。
            note: 補足説明。
        """
        self.axioms(
            name, [AxiomGroup(symbol=name, title="", ref=ref, axioms=tuple(axioms), note=note)]
        )

    def table(self, title: str, columns: Sequence[str], rows: Sequence[Sequence[str]]) -> None:
        """表を表示・記録する.

        Args:
            title: 表題。
            columns: 列の見出し。
            rows: 行 (各セルは文字列)。
        """
        self._add(
            {
                "kind": "table",
                "title": title,
                "columns": list(columns),
                "rows": [list(r) for r in rows],
            }
        )
        t = Table(title=escape(title), title_justify="left")
        for c in columns:
            t.add_column(escape(c))
        for r in rows:
            t.add_row(*(escape(c) for c in r))
        console.print(t)

    def situation_tree(self, item: ItemTrace) -> None:
        """状況の木を記録する (ビューア専用。ターミナルには節点の数だけ出す).

        Args:
            item: 状況の木 (kind が ``"situation_tree"`` の内容)。
        """
        self._add(item)
        if item["kind"] == "situation_tree":
            console.print(f"[dim](状況の木: {len(item['nodes'])} 節点をビューア用に記録)[/dim]")

    # -- 検査 ---------------------------------------------------------------

    def _check(self, check: CheckTrace) -> bool:
        """検査結果を表示・記録し、期待と違えば失敗として数える.

        Args:
            check: 検査結果。

        Returns:
            期待どおりなら True。
        """
        self._add({"kind": "check", "check": check})
        mark = "[green]✓[/green]" if check["ok"] else "[red]✗[/red]"
        ref = f" [dim]{escape(check['ref'])}[/dim]" if check["ref"] else ""
        console.print(f"{mark} {escape(check['label'])}{ref}")
        expected = "" if check["ok"] else f"  (期待: {escape(check['expected'])})"
        console.print(f"    結果: {escape(check['actual'])}{expected}")
        if check["detail"]:
            for line in check["detail"].splitlines():
                console.print(f"    [dim]{escape(line)}[/dim]")
        if not check["ok"]:
            self.failures.append(check["label"])
        return check["ok"]

    def expect(
        self,
        label: str,
        *,
        ok: bool,
        actual: str,
        expected: str = "",
        ref: str = "",
        detail: str = "",
    ) -> bool:
        """一般の検査を表示・記録する.

        Args:
            label: 何を検査したか。
            ok: 期待どおりか。
            actual: 実際の結果の表示。
            expected: 期待した結果の表示。
            ref: 本書での出典。
            detail: 補足 (反例や理由など)。

        Returns:
            期待どおりなら True。
        """
        return self._check(
            {
                "label": label,
                "ref": ref,
                "expected": expected,
                "actual": actual,
                "ok": ok,
                "detail": detail,
            }
        )

    def expect_entailment(
        self, label: str, result: Entailment, expected: Verdict, *, ref: str = "", detail: str = ""
    ) -> bool:
        """帰結判定の検査を表示・記録する.

        Args:
            label: 何を検査したか。
            result: 帰結判定の結果。
            expected: 期待した判定。
            ref: 本書での出典。
            detail: 補足 (反例や理由など)。
                unknown のときは Z3 の理由を後ろに足す。

        Returns:
            期待どおりなら True。
        """
        extra = f"\nZ3: {result.reason}" if result.reason else ""
        return self.expect(
            label,
            ok=result.verdict is expected,
            actual=result.verdict.value,
            expected=expected.value,
            ref=ref,
            detail=detail + extra,
        )

    def expect_sat(
        self,
        label: str,
        result: SatResult,
        expected: Satisfiability,
        *,
        ref: str = "",
        detail: str = "",
    ) -> bool:
        """充足可能性の検査を表示・記録する.

        Args:
            label: 何を検査したか。
            result: 充足可能性の判定結果。
            expected: 期待した判定。
            ref: 本書での出典。
            detail: 補足 (反例や理由など)。

        Returns:
            期待どおりなら True。
        """
        return self.expect(
            label,
            ok=result.status is expected,
            actual=result.status.value,
            expected=expected.value,
            ref=ref,
            detail=detail,
        )

    def finish(self) -> ExampleTrace:
        """検査の結果をまとめて表示する.

        Returns:
            この例題の記録。

        Raises:
            CheckFailedError: 期待と違う検査があったとき (記録は例外の ``trace`` に入る)。
        """
        checks = [
            it["check"]
            for sec in self.trace["sections"]
            for it in sec["items"]
            if it["kind"] == "check"
        ]
        console.print()
        if self.failures:
            console.print(
                f"[red bold]{len(self.failures)} / {len(checks)} 件の検査が期待と違った[/red bold]"
            )
            raise CheckFailedError(", ".join(self.failures), self.trace)
        console.print(f"[green bold]すべての検査 ({len(checks)} 件) が期待どおり[/green bold]")
        return self.trace


def towers_text(state: StateTrace) -> str:
    """ブロック世界の状態を ASCII で描く (下が机).

    例::

            [C]
        [A] [B]
        ────────
        手: -

    Args:
        state: ブロック世界の状態。

    Returns:
        複数行の文字列 (塔、机の線、手に持っているブロック)。
    """
    towers = state["towers"]
    height = max((len(t) for t in towers), default=0)
    width = 4
    lines = [
        "".join(f"[{t[level]}] " if level < len(t) else " " * width for t in towers).rstrip()
        for level in reversed(range(height))
    ]
    lines.append("─" * max(width * len(towers), width))
    lines.append(f"手: {state['holding'] or '-'}")
    return "\n".join(lines)
