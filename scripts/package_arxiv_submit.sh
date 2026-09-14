#!/usr/bin/env bash
# Build PlatonicSolids.tex and zip everything arXiv needs to compile it (pdfLaTeX).
#
# Template: lrsodincic/scripts/package_arxiv_submit.sh. Dependency-graph
# blueprints live in figures/*.mmd and are rendered to figures/*.png by
# build_pdf.py. The PDF appendix indexes modules with GitHub links; the zip
# still ships Lean sources for reproducibility. Contents: 00README.json,
# the generated .tex, Lean sources, and rendered figure PNGs (arXiv rejects PDF figures).
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
if [[ "${1:-}" != "--skip-tex-build" ]]; then
  echo "==> Regenerating ${TEX} + PlatonicSolids.pdf"
  python3 build_pdf.py
fi

mapfile -t FIGURE_PNGS < <(find figures -name '*.png' | sort)
if [[ ${#FIGURE_PNGS[@]} -eq 0 ]]; then
  echo "error: no figures/*.png (run python3 build_pdf.py to render from *.mmd)" >&2
  exit 1
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
figures = sorted(p.as_posix() for p in Path("figures").glob("*.png"))

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
  "${FIGURE_PNGS[@]}"

echo "wrote $ZIP ($(du -h "$ZIP" | cut -f1))"
echo "Contents:"
zipinfo -1 "$ZIP" | sed 's/^/  /'
echo
echo "Upload $ZIP to arXiv (pdfLaTeX; UTF-8 Lean listings render via the listings literate"
echo "table). On arXiv Add Files: Delete All before uploading (uploads merge, they do not"
echo "replace). On arXiv Review Files: if a .lean file is marked for deletion, UNCHECK it."
