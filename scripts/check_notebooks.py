"""Run Pyright on notebook code cells, reporting notebook cell and line numbers."""

import json
import subprocess
import sys
import tempfile
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent


def main() -> int:
    notebooks = sorted(ROOT.rglob("*.ipynb"))
    notebooks = [p for p in notebooks if not any(part.startswith(".") for part in p.relative_to(ROOT).parts)]
    if not notebooks:
        print("No notebooks found.")
        return 0

    with tempfile.TemporaryDirectory(prefix="pyright-notebooks-", dir=ROOT) as directory:
        paths = {}
        for index, notebook in enumerate(notebooks):
            data = json.loads(notebook.read_text(encoding="utf-8"))
            lines = []
            locations = []
            for cell_number, cell in enumerate(data["cells"], start=1):
                if cell["cell_type"] != "code":
                    continue
                source = "".join(cell["source"])
                for line_number, line in enumerate(source.splitlines(), start=1):
                    lines.append(line)
                    locations.append((cell_number, line_number))
                lines.append("")
                locations.append((cell_number, max(1, len(source.splitlines()))))
            path = Path(directory) / f"notebook_{index}.py"
            path.write_text("\n".join(lines) + "\n", encoding="utf-8")
            paths[str(path)] = (notebook, locations)

        result = subprocess.run(
            [sys.executable, "-m", "pyright", "--outputjson", *paths],
            cwd=ROOT, capture_output=True, text=True, check=False,
        )
        if result.returncode not in (0, 1):
            print(result.stderr or result.stdout, file=sys.stderr)
            return result.returncode
        report = json.loads(result.stdout)
        if report["summary"]["filesAnalyzed"] != len(paths):
            print("Pyright did not analyze every notebook.", file=sys.stderr)
            return 1
        for diagnostic in report["generalDiagnostics"]:
            notebook, locations = paths[diagnostic["file"]]
            line = diagnostic["range"]["start"]["line"]
            cell, cell_line = locations[line]
            column = diagnostic["range"]["start"]["character"] + 1
            rule = diagnostic.get("rule", "")
            print(f"{notebook.relative_to(ROOT)}: cell {cell}, line {cell_line}, column {column}: "
                  f"{diagnostic['severity']}: {diagnostic['message']} ({rule})")
        summary = report["summary"]
        print(f"{summary['errorCount']} errors, {summary['warningCount']} warnings")
        return result.returncode


if __name__ == "__main__":
    raise SystemExit(main())
