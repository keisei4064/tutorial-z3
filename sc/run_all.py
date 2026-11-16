"""すべての例題を実行し，検査結果をまとめ，ビューア用の JSON を書き出す

使い方 (リポジトリのルートで)::

    uv run python -m sc.run_all            # sc/out/trace.json に書き出す
    uv run python -m sc.run_all out.json   # 書き出し先を指定

どれかの例題で検査が期待と違えば終了コード 1 で終わる
"""

import sys
import time
from collections.abc import Callable
from pathlib import Path

from rich.table import Table

from sc.examples import (
    blocks_world,
    blocks_world_move,
    induction,
    regression_toy,
    suitcase,
    yale_shooting,
)
from sc.viz.export import ExampleTrace, write_trace
from sc.viz.terminal import CheckFailedError, console

EXAMPLES: tuple[tuple[str, Callable[[], ExampleTrace]], ...] = (
    ("regression_toy", regression_toy.run),
    ("yale_shooting", yale_shooting.run),
    ("blocks_world", blocks_world.run),
    ("blocks_world_move", blocks_world_move.run),
    ("suitcase", suitcase.run),
    ("induction", induction.run),
)

DEFAULT_OUT = Path(__file__).resolve().parent / "out" / "trace.json"


def _count_checks(trace: ExampleTrace) -> tuple[int, int]:
    """例題の記録から，期待どおりの検査の数と全体の数を数える

    Args:
        trace: 例題の記録

    Returns:
        (期待どおりの数, 全体の数)
    """
    checks = [
        it["check"] for sec in trace["sections"] for it in sec["items"] if it["kind"] == "check"
    ]
    return sum(c["ok"] for c in checks), len(checks)


def main(argv: list[str]) -> int:
    """すべての例題を実行する

    Args:
        argv: コマンドライン引数 (argv[1] があれば書き出し先)

    Returns:
        終了コード (すべて期待どおりなら 0，そうでなければ 1)
    """
    out = Path(argv[1]) if len(argv) > 1 else DEFAULT_OUT
    traces: list[ExampleTrace] = []
    rows: list[tuple[str, str, str]] = []
    for name, run in EXAMPLES:
        start = time.perf_counter()
        try:
            trace = run()
        except CheckFailedError as err:
            trace = err.trace
        elapsed = time.perf_counter() - start
        traces.append(trace)
        ok, total = _count_checks(trace)
        rows.append((name, f"{ok} / {total}", f"{elapsed:.1f}"))

    write_trace(out, traces)
    table = Table(title="まとめ", title_justify="left")
    table.add_column("例題")
    table.add_column("期待どおりの検査")
    table.add_column("秒")
    for row in rows:
        style = "green" if row[1].split(" / ")[0] == row[1].split(" / ")[1] else "red"
        table.add_row(*row, style=style)
    console.print()
    console.print(table)
    console.print(f"ビューア用データ: {out}")
    failed = [r[0] for r in rows if r[1].split(" / ")[0] != r[1].split(" / ")[1]]
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
