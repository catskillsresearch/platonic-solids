#!/usr/bin/env bash
# Build PlatonicSolids.tex and zip everything arXiv needs to compile it (pdfLaTeX).
#
# Template: lrsodincic/scripts/package_arxiv_submit.sh. This note has no mermaid
# figures and inlines Lean via \lstinputlisting of PlatonicSolids.lean plus the
# gist-sized modules under PlatonicSolids/, so the zip is 00README.json, the
# generated .tex, and those Lean sources.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

TEX="PlatonicSolids.tex"
OUT_DIR="dist"
ZIP="${OUT_DIR}/arxiv_submit.zip"

LEAN_FILES=(
  PlatonicSolids.lean
  Challenge.lean
  Solution.lean
  PlatonicSolids/Angles.lean
  PlatonicSolids/Classification.lean
  PlatonicSolids/CompatibleTriples.lean
  PlatonicSolids/CompletingSquare.lean
  PlatonicSolids/D3IffPlatonic.lean
  PlatonicSolids/DetFormula.lean
  PlatonicSolids/EulerBetti.lean
  PlatonicSolids/GramMatrix.lean
  PlatonicSolids/Incidence.lean
  PlatonicSolids/LeadingMinors.lean
  PlatonicSolids/PlatonicPair.lean
  PlatonicSolids/QuadForm.lean
  PlatonicSolids/Reciprocal.lean
  PlatonicSolids/Regular4.lean
  PlatonicSolids/SignTable.lean
  PlatonicSolids/Sylvester.lean
  PlatonicSolids/TrailingMinor.lean
  PlatonicSolids/TrigValues.lean
)

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

echo "==> Writing 00README.json (mark Lean listings as include so arXiv does not drop them)"
python3 - <<'PY'
import json
from pathlib import Path

lean = [
    "PlatonicSolids.lean",
    "Challenge.lean",
    "Solution.lean",
] + sorted(p.as_posix() for p in Path("PlatonicSolids").glob("*.lean"))

readme = {
    "process": {"compiler": "pdflatex"},
    "sources": (
        [{"filename": "PlatonicSolids.tex", "usage": "toplevel"}]
        + [{"filename": name, "usage": "include"} for name in lean]
    ),
}
Path("00README.json").write_text(json.dumps(readme, indent=2) + "\n")
print(f"  {len(readme['sources'])} sources")
PY

echo "==> Packaging"
zip -r "$ZIP" \
  00README.json \
  "$TEX" \
  "${LEAN_FILES[@]}"

echo "wrote $ZIP ($(du -h "$ZIP" | cut -f1))"
echo "Contents:"
zipinfo -1 "$ZIP" | sed 's/^/  /'
echo
echo "Upload $ZIP to arXiv (pdfLaTeX; UTF-8 Lean listings render via the listings literate"
echo "table). On arXiv Add Files: Delete All before uploading (uploads merge, they do not"
echo "replace). On arXiv Review Files: if a .lean file is marked for deletion, UNCHECK it."
