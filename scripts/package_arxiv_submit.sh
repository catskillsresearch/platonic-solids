#!/usr/bin/env bash
# Build PlatonicSolids.tex and zip everything arXiv needs to compile it (pdfLaTeX).
#
# Template: lrsodincic/scripts/package_arxiv_submit.sh. Dependency-graph
# blueprints live in figures/*.mmd and are rendered to figures/*.pdf by
# build_pdf.py. Lean is inlined via \lstinputlisting of PlatonicSolids.lean,
# the gist-sized modules under PlatonicSolids/, and the SingularExcision/
# subtree. The zip is 00README.json, the generated .tex, those Lean
# sources, and the rendered figure PDFs.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

TEX="PlatonicSolids.tex"
OUT_DIR="dist"
ZIP="${OUT_DIR}/arxiv_submit.zip"

mapfile -t LEAN_FILES < <(
  printf '%s\n' PlatonicSolids.lean Challenge.lean Solution.lean
  find PlatonicSolids -name '*.lean' | sort
)
mapfile -t FIGURE_PDFS < <(find figures -name '*.pdf' | sort)

if [[ "${1:-}" != "--skip-tex-build" ]]; then
  echo "==> Regenerating ${TEX} + PlatonicSolids.pdf"
  python3 build_pdf.py
fi

missing=0
if [[ ! -f "$TEX" ]]; then
  echo "error: missing $TEX (run python3 build_pdf.py)" >&2
  missing=1
fi
for f in "${LEAN_FILES[@]}"; do
  if [[ ! -f "$f" ]]; then
    echo "error: missing $f" >&2
    missing=1
  fi
done
if [[ "$missing" -ne 0 ]]; then
  exit 1
fi

mkdir -p "$OUT_DIR"
rm -f "$ZIP"

echo "==> Writing 00README.json (mark Lean listings and figures as include)"
python3 - <<'PY'
import json
from pathlib import Path

lean = [
    "PlatonicSolids.lean",
    "Challenge.lean",
    "Solution.lean",
] + sorted(p.as_posix() for p in Path("PlatonicSolids").rglob("*.lean"))
figures = sorted(p.as_posix() for p in Path("figures").glob("*.pdf"))

readme = {
    "process": {"compiler": "pdflatex"},
    "sources": (
        [{"filename": "PlatonicSolids.tex", "usage": "toplevel"}]
        + [{"filename": name, "usage": "include"} for name in lean + figures]
    ),
}
Path("00README.json").write_text(json.dumps(readme, indent=2) + "\n")
print(f"  {len(readme['sources'])} sources")
PY

echo "==> Packaging"
zip -r "$ZIP" \
  00README.json \
  "$TEX" \
  "${LEAN_FILES[@]}" \
  "${FIGURE_PDFS[@]}"

echo "wrote $ZIP ($(du -h "$ZIP" | cut -f1))"
echo "Contents:"
zipinfo -1 "$ZIP" | sed 's/^/  /'
echo
echo "Upload $ZIP to arXiv (pdfLaTeX; UTF-8 Lean listings render via the listings literate"
echo "table). On arXiv Add Files: Delete All before uploading (uploads merge, they do not"
echo "replace). On arXiv Review Files: if a .lean file is marked for deletion, UNCHECK it."
