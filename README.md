[![Lean 4](https://img.shields.io/github/actions/workflow/status/catskillsresearch/platonic-solids/build.yml?label=Lean%204)](https://github.com/catskillsresearch/platonic-solids/actions/workflows/build.yml)

# Platonic Solids

A Lean 4 / Mathlib classification of the regular convex polyhedra in
\(\mathbb{R}^3\) (the Platonic solids) and the regular convex polychora in
\(\mathbb{R}^4\). Mathlib is the only Lake dependency.

In dimension 3, Euler's formula \(V - E + F = 2\) together with regularity
incidence \(pF = 2E\), \(qV = 2E\) yields the Diophantine inequality
\((p-2)(q-2) < 4\), hence exactly five Platonic pairs. The same identities
force \(E > 0\) without a geometric non-degeneracy axiom.

The supporting topology proves singular \(H_n(S^n;R)\cong R\) for \(n>0\)
from open-cover excision. A chain-level bridge additionally proves that any
finite \(2\)-complex quasi-isomorphic to singular chains of a space of the
homotopy type of \(S^2\) has Betti profile \((1,0,1)\), and therefore yields
the Platonic classification. Constructing that comparison from a concrete
polyhedral cellulation is a separate geometric input.

In dimension 4, \(\chi(S^3) = 0\) supplies no bound. The six regular convex
4-polytopes are the Platonic-cell / Platonic-vertex-figure triples whose
Schläfli Gram determinant
\(\Delta(p,q,r) = \sin^2(\pi/p)\sin^2(\pi/r) - \cos^2(\pi/q)\) is strictly
positive.

The **Palomar compared family** is `platonic_solids_3d`,
`edges_pos_of_regular`, and `regular_polychora_classification`. The
development contains **zero axioms, zero admits, and zero `sorry`s**
outside the deliberate holes in `Challenge.lean`.

## Files

| File | Role |
|---|---|
| `PlatonicSolids.md` | Paper (topology in 3D, Coxeter in 4D) — the source of truth |
| `PlatonicSolids.lean` | Root import of the section-sized modules |
| `PlatonicSolids/*.lean` | Gist-sized proofs, one file per paper paragraph |
| `Challenge.lean` | Palomar statement of record: the compared family with deliberate `sorry`s |
| `Solution.lean` | Palomar solution module: imports `PlatonicSolids` |
| `comparator.json` | Comparator config naming the three theorems and supporting definitions |
| `formalization.yaml` | Palomar / formalization.yaml v0.4 metadata and disclosures |
| `PROVENANCE.md` | Origin of this package and relationship to the template repos |
| `PlatonicSolids.pdf` | Paper PDF (committed deliverable; synced from `view.pdf`) |
| `view.pdf` | Official arXiv AutoTeX build (pdfLaTeX), once submitted |
| `build_pdf.py` | `PlatonicSolids.md` → `PlatonicSolids.tex` → `PlatonicSolids.pdf`, Lean source inlined as an appendix |
| `scripts/package_arxiv_submit.sh` | `dist/arxiv_submit.zip` for arXiv (pdfLaTeX + Lean listing) |
| `scripts/tex_preamble_arxiv.tex` | Listings / unicode preamble used by the PDF build |
| `scripts/palomar_preflight.sh` | Local / CI replica of Palomar mechanical verification |
| `LICENSE` | Apache License 2.0 |
| `NOTICE` | Copyright and third-party attribution |

`PlatonicSolids.tex` is generated and git-ignored. The title page lists the
author, ORCID, Catskills Research Company, and the GitHub URL. After Palomar
registration, the registry URL is added beside it.

## Build the Lean

Requires [elan](https://github.com/leanprover/elan) (or an equivalent Lean 4
install). The pin is `leanprover/lean4:v4.30.0`.

```bash
lake exe cache get
lake build
```

Open `PlatonicSolids.lean` in this repository so the Lean server uses this
package's `lakefile.toml`. `lake build` also typechecks `Challenge.lean` and
`Solution.lean`.

`Challenge.lean` is the statement of record: it imports only Mathlib,
declares the definitions the family uses, and leaves the three compared
theorems as `sorry`. A reader who wants to check *what* has been proved
should read that file. The proofs are the gist-sized modules under
`PlatonicSolids/`, imported by `PlatonicSolids.lean` and exposed to
Comparator through `Solution.lean`. Each paper paragraph names its file.

## Palomar packaging

Local mechanical readiness (CI runs this on every push):

```bash
bash scripts/palomar_preflight.sh --mechanical-only
```

Mechanical green means Challenge and Solution types match under Comparator
rules and Solution sources contain no `sorry`. It does **not** assign a
Palomar registry ID. Actual registration requires a public GitHub repository,
a full 40-character commit SHA, the root project path, and explicit selection
of `comparator.json` at [submit.palomar-registry.org](https://submit.palomar-registry.org/).

## Build the paper

Needs `pandoc` and `latexmk`.

```bash
python3 build_pdf.py
bash scripts/package_arxiv_submit.sh   # dist/arxiv_submit.zip (rebuilds the PDF first)
```

`dist/arxiv_submit.zip` is the arXiv upload: `PlatonicSolids.tex`, the
Lean sources (root import plus `PlatonicSolids/*.lean`, listed in the
appendix), and `00README.json` so AutoTeX keeps those files and compiles
with pdfLaTeX. On arXiv Add Files, Delete All before uploading; on Review
Files, uncheck deletion if a `.lean` file is marked. After a successful
arXiv compile, save the preview PDF as `view.pdf` and copy it to
`PlatonicSolids.pdf` so the committed deliverable matches AutoTeX.

## License

Copyright 2026 Lars Warren Ericson. Licensed under the Apache License,
Version 2.0. See `LICENSE` and `NOTICE`.
