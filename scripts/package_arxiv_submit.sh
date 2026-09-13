#!/usr/bin/env bash
# Build PlatonicSolids.tex and zip everything arXiv needs to compile it (pdfLaTeX).
#
# Template: lrsodincic/scripts/package_arxiv_submit.sh. This note has no mermaid
# figures and inlines Lean via \lstinputlisting{PlatonicSolids.lean}, so the zip is
# just 00README.json + the generated .tex + the Lean source.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

TEX="PlatonicSolids.tex"
LEAN="PlatonicSolids.lean"
OUT_DIR="dist"
ZIP="${OUT_DIR}/arxiv_submit.zip"

if [[ "${1:-}" != "--skip-tex-build" ]]; then
  echo "==> Regenerating ${TEX} + PlatonicSolids.pdf"
  python3 build_pdf.py
fi

missing=0
if [[ ! -f "$TEX" ]]; then
  echo "error: missing $TEX (run python3 build_pdf.py)" >&2
  missing=1
fi
if [[ ! -f "$LEAN" ]]; then
  echo "error: missing $LEAN" >&2
  missing=1
fi
if [[ "$missing" -ne 0 ]]; then
  exit 1
fi

mkdir -p "$OUT_DIR"
rm -f "$ZIP"

echo "==> Writing 00README.json (mark the Lean listing as include so arXiv does not drop it)"
python3 - <<'PY'
import json
from pathlib import Path

readme = {
    "process": {"compiler": "pdflatex"},
    "sources": [
        {"filename": "PlatonicSolids.tex", "usage": "toplevel"},
        {"filename": "PlatonicSolids.lean", "usage": "include"},
    ],
}
Path("00README.json").write_text(json.dumps(readme, indent=2) + "\n")
print(f"  {len(readme['sources'])} sources")
PY

echo "==> Packaging"
zip -r "$ZIP" \
  00README.json \
  "$TEX" \
  "$LEAN"

echo "wrote $ZIP ($(du -h "$ZIP" | cut -f1))"
echo "Contents:"
zipinfo -1 "$ZIP" | sed 's/^/  /'
echo
echo "Upload $ZIP to arXiv (pdfLaTeX; UTF-8 Lean listings render via the listings literate"
echo "table). On arXiv Add Files: Delete All before uploading (uploads merge, they do not"
echo "replace). On arXiv Review Files: if PlatonicSolids.lean is marked for deletion, UNCHECK it."
