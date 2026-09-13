#!/usr/bin/env python3
# Copyright (c) 2026 Lars Warren Ericson.
# Licensed under the Apache License, Version 2.0. See LICENSE and NOTICE.
"""Build PlatonicSolids.tex and PlatonicSolids.pdf from PlatonicSolids.md.

Adapted from the lrsodincic / CARDB PDF pipeline:

  1. lift the `# ...` title and Abstract paragraph into \\title and `abstract`;
  2. pandoc the body, demoting headings by one so `##` sections become \\section;
  3. render fenced code with `listings` in the shared `leanbox` style;
  4. reuse scripts/tex_preamble_arxiv.tex, plus glyphs this note uses that the
     original arxiv paper does not;
  5. compile with latexmk.

The generated `.tex` lives in this directory. `PlatonicSolids.tex` is git-ignored;
`PlatonicSolids.pdf` is the committed deliverable.
"""

from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
SRC = HERE / "PlatonicSolids.md"
LEAN = HERE / "PlatonicSolids.lean"
LEAN_DIR = HERE / "PlatonicSolids"
FIGURES = HERE / "figures"

# Paper order: each file is a gist-sized chunk next to one exposition paragraph.
LEAN_MODULES = [
    (LEAN, "Root import of the section-sized modules"),
    (LEAN_DIR / "RadialProjection.lean", r"Frontier of a bounded convex body is homeomorphic to the sphere"),
    (LEAN_DIR / "EulerPoincare.lean", r"Algebraic Euler--Poincar\'e in dimensions $2$ and $3$"),
    (LEAN_DIR / "SingularHomology.lean", r"Singular $H_0(S^n)$, $H_*(S^0)$, homotopy invariance"),
    (LEAN_DIR / "RelativeHomology.lean", r"Relative singular homology and the LES of a pair"),
    (LEAN_DIR / "MayerVietoris.lean", r"Mayer--Vietoris of an excisive triad; stereographic cover of $S^n$"),
    (LEAN_DIR / "SingularExcision.lean", r"Root import of barycentric subdivision and small-chain excision"),
    (LEAN_DIR / "SingularExcision" / "Algebra.lean", r"Ungraded subdivision retract on an abelian group"),
    (LEAN_DIR / "SingularExcision" / "AffineSubdivision.lean", r"Affine barycentric subdivision and prism"),
    (LEAN_DIR / "SingularExcision" / "AffineRealization.lean", r"Realization of affine simplices in a space"),
    (LEAN_DIR / "SingularExcision" / "Mesh.lean", r"Lebesgue number and mesh-ratio $n/(n+1)$"),
    (LEAN_DIR / "SingularExcision" / "BarycentricGeometry.lean", r"Diameter of barycentric pieces and eventual smallness"),
    (LEAN_DIR / "SingularExcision" / "SingularChains.lean", r"Singular $\mathrm{Sd}$ as a chain map and the prism homotopy"),
    (LEAN_DIR / "SingularExcision" / "ModuleSupport.lean", r"Finite coproduct support in $\mathrm{ModuleCat}$"),
    (LEAN_DIR / "SingularExcision" / "Subcomplexes.lean", r"Lands-in and small singular subcomplexes"),
    (LEAN_DIR / "SingularExcision" / "DegreewisePushout.lean", r"Degreewise pushout of small chains"),
    (LEAN_DIR / "SingularExcision" / "CokernelPushout.lean", r"Cokernel model of a preadditive pushout"),
    (LEAN_DIR / "SingularExcision" / "CoverChains.lean", r"Cover chains isomorphic to small singular chains"),
    (LEAN_DIR / "SingularExcision" / "SmallChains.lean", r"Small-chain subgroup, invariance, and the retract"),
    (LEAN_DIR / "SingularExcision" / "OpenCoverQI.lean", r"Open-cover quasi-isomorphism and $\mathtt{IsExcisiveSubspaces}$"),
    (LEAN_DIR / "SphereSingularHomology.lean", r"Stereographic $U\cap V\simeq_h S^{n-1}$ and $H_{n+1}(S^{n+1})\cong H_n(S^n)$"),
    (LEAN_DIR / "Sphere2Homology.lean", r"Cellular $H_*(S^2;\mathbb{Q})$ of the tetrahedron surface"),
    (LEAN_DIR / "Sphere3Homology.lean", r"Cellular $H_*(S^3;\mathbb{Q})$ of the $4$-simplex boundary"),
    (LEAN_DIR / "EulerBetti.lean", r"Betti arithmetic of $\chi(S^2)=2$ and $\chi(S^3)=0$"),
    (LEAN_DIR / "PlatonicPair.lean", "The five solutions of the Platonic Diophantine inequality"),
    (LEAN_DIR / "Reciprocal.lean", r"$1/p+1/q>1/2$ iff the integer inequality"),
    (LEAN_DIR / "Incidence.lean", r"Regularity incidence plus Euler force a Platonic pair and $E>0$"),
    (LEAN_DIR / "Angles.lean", r"$\pi/n\in(0,\pi/2)$ so sine and cosine are positive"),
    (LEAN_DIR / "GramMatrix.lean", "Schläfli Gram matrix and the scalar $\\Delta$"),
    (LEAN_DIR / "LeadingMinors.lean", r"Closed forms of the leading minors $D_1,D_2,D_3$"),
    (LEAN_DIR / "TrailingMinor.lean", "Trailing $3\\times 3$ minor is the vertex-figure cell minor"),
    (LEAN_DIR / "D3IffPlatonic.lean", r"$D_3>0$ iff the cell is Platonic"),
    (LEAN_DIR / "QuadForm.lean", "Quadratic form of the Gram matrix"),
    (LEAN_DIR / "CompletingSquare.lean", "LDL / completing-the-square identity"),
    (LEAN_DIR / "DetFormula.lean", r"$\det M=\Delta$"),
    (LEAN_DIR / "Sylvester.lean", "Sylvester: positive definite iff leading minors are positive"),
    (LEAN_DIR / "TrigValues.lean", r"Exact $\\sin^2(\\pi/n)$ and $\\cos^2(\\pi/n)$ for $n\\in\\{3,4,5\\}$"),
    (LEAN_DIR / "CompatibleTriples.lean", "The eleven Platonic-compatible Schläfli triples"),
    (LEAN_DIR / "SignTable.lean", r"Sign of $\Delta$ on those eleven triples"),
    (LEAN_DIR / "Regular4.lean", "The six regular convex 4-polytopes"),
    (LEAN_DIR / "Classification.lean", r"$\Delta>0$ (equivalently $M$ positive definite) iff one of the six"),
    (HERE / "Challenge.lean", "Palomar statement of record (deliberate sorries)"),
    (HERE / "Solution.lean", "Palomar solution module: imports PlatonicSolids"),
]
OUT_TEX = HERE / "PlatonicSolids.tex"
OUT_PDF = HERE / "PlatonicSolids.pdf"
PREAMBLE = HERE / "scripts" / "tex_preamble_arxiv.tex"

AUTHOR = "Lars Warren Ericson"
COMPANY = "Catskills Research Company"
GITHUB_URL = r"https://github.com/catskillsresearch/platonic-solids"
ORCID = "0000-0001-8299-9361"
EMAIL = "lars.ericson@catskillsresearch.com"

# Glyphs used here but absent from the shared preamble's `literate` table
# (listings) and `\newunicodechar` declarations (prose).
EXTRA_LITERATE = r"""    {ä}{{\"{a}}}1
    {Ä}{{\"{A}}}1
    {é}{{\'{e}}}1
    {²}{{\textsuperscript{2}}}1
    {₄}{{\textsubscript{4}}}1
    {√}{{\ensuremath{\sqrt{}}}}1
    {Δ}{{\ensuremath{\Delta}}}1
    {ℝ}{{\ensuremath{\mathbb{R}}}}1
    {ℕ}{{\ensuremath{\mathbb{N}}}}1
    {ℤ}{{\ensuremath{\mathbb{Z}}}}1
    {ℚ}{{\ensuremath{\mathbb{Q}}}}1
    {χ}{{\ensuremath{\chi}}}1
    {π}{{\ensuremath{\pi}}}1
    {³}{{\textsuperscript{3}}}1
    {γ}{{\ensuremath{\gamma}}}1
    {ᵥ}{{\textsubscript{v}}}1
    {∑}{{\ensuremath{\sum}}}1
    {⬝}{{\ensuremath{\cdot}}}1
    {−}{{\ensuremath{-}}}1
    {∂}{{\ensuremath{\partial}}}1
    {ₗ}{{\textsubscript{l}}}1
    {ₕ}{{\textsubscript{h}}}1
    {ⁿ}{{\textsuperscript{n}}}1
    {⁰}{{\textsuperscript{0}}}1
    {±}{{\ensuremath{\pm}}}1
    {ε}{{\ensuremath{\varepsilon}}}1
    {’}{{\textquoteright}}1
    {∐}{{\ensuremath{\coprod}}}1
    {≫}{{\ensuremath{\gg}}}1
    {⊂}{{\ensuremath{\subset}}}1
    {𝟙}{{\ensuremath{\mathbb{1}}}}1
    {⊕}{{\ensuremath{\oplus}}}1
    {⊞}{{\ensuremath{\boxplus}}}1
    {♯}{{\ensuremath{\sharp}}}1
    {ᗮ}{{\ensuremath{^{\perp}}}}1
    {δ}{{\ensuremath{\delta}}}1
    {ᶜ}{{\ensuremath{^{\mathrm{c}}}}}3
    {∙}{{\ensuremath{\cdot}}}1
    {‖}{{\ensuremath{\lVert}}}1
    {•}{{\ensuremath{\bullet}}}1
    {¹}{{\textsuperscript{1}}}1
    {ᵒ}{{\textsuperscript{o}}}1
    {ᵖ}{{\textsuperscript{p}}}1
    {⦋}{{[}}1
    {⦌}{{]}}1
    {ρ}{{\ensuremath{\rho}}}1
"""

EXTRA_UNICODECHAR = r"""
% --- Glyphs specific to this document ---
\newunicodechar{ä}{\"{a}}
\newunicodechar{Ä}{\"{A}}
\newunicodechar{é}{\'{e}}
\newunicodechar{²}{\textsuperscript{2}}
\newunicodechar{₄}{\textsubscript{4}}
\newunicodechar{√}{\ensuremath{\sqrt{}}}
\newunicodechar{Δ}{\ensuremath{\Delta}}
\newunicodechar{ℝ}{\ensuremath{\mathbb{R}}}
\newunicodechar{ℕ}{\ensuremath{\mathbb{N}}}
\newunicodechar{ℤ}{\ensuremath{\mathbb{Z}}}
\newunicodechar{ℚ}{\ensuremath{\mathbb{Q}}}
\newunicodechar{χ}{\ensuremath{\chi}}
\newunicodechar{π}{\ensuremath{\pi}}
\newunicodechar{³}{\textsuperscript{3}}
\newunicodechar{γ}{\ensuremath{\gamma}}
\newunicodechar{ᵥ}{\textsubscript{v}}
\newunicodechar{∑}{\ensuremath{\sum}}
\newunicodechar{⬝}{\ensuremath{\cdot}}
\newunicodechar{−}{\ensuremath{-}}
\newunicodechar{∂}{\ensuremath{\partial}}
\newunicodechar{ₗ}{\textsubscript{l}}
\newunicodechar{ₕ}{\textsubscript{h}}
\newunicodechar{ⁿ}{\textsuperscript{n}}
\newunicodechar{⁰}{\textsuperscript{0}}
\newunicodechar{±}{\ensuremath{\pm}}
\newunicodechar{ε}{\ensuremath{\varepsilon}}
\newunicodechar{∐}{\ensuremath{\coprod}}
\newunicodechar{≫}{\ensuremath{\gg}}
\newunicodechar{⊂}{\ensuremath{\subset}}
\newunicodechar{𝟙}{\ensuremath{\mathbb{1}}}
\newunicodechar{⊕}{\ensuremath{\oplus}}
\newunicodechar{⦃}{\textbraceleft\textbraceleft}
\newunicodechar{⦄}{\textbraceright\textbraceright}
\newunicodechar{⊞}{\ensuremath{\boxplus}}
\newunicodechar{♯}{\ensuremath{\sharp}}
\newunicodechar{ᗮ}{\ensuremath{^{\perp}}}
\newunicodechar{δ}{\ensuremath{\delta}}
\newunicodechar{ᶜ}{\ensuremath{^{\mathrm{c}}}}
\newunicodechar{∙}{\ensuremath{\cdot}}
\newunicodechar{‖}{\ensuremath{\lVert}}
\newunicodechar{•}{\ensuremath{\bullet}}
\newunicodechar{¹}{\textsuperscript{1}}
\newunicodechar{ᵒ}{\textsuperscript{o}}
\newunicodechar{ᵖ}{\textsuperscript{p}}
\newunicodechar{⦋}{[}
\newunicodechar{⦌}{]}
\newunicodechar{ρ}{\ensuremath{\rho}}
"""


FENCE_RE = re.compile(r"^```[^\n]*\n(.*?)^```[ \t]*$", re.M | re.S)
PLACEHOLDER = "PLATONICCODEBLOCK{}ENDBLOCK"


def render_mermaid_figures() -> list[Path]:
    """Render every ``figures/*.mmd`` blueprint to a PDF for ``\\includegraphics``."""
    rendered: list[Path] = []
    puppeteer = FIGURES / "puppeteer.json"
    for src in sorted(FIGURES.glob("*.mmd")):
        out = src.with_suffix(".pdf")
        cmd = [
            "mmdc",
            "-i",
            str(src),
            "-o",
            str(out),
            "-t",
            "neutral",
            "-b",
            "white",
            "-f",
            "-p",
            str(puppeteer),
        ]
        proc = subprocess.run(cmd, capture_output=True, text=True, check=False)
        if proc.returncode != 0 or not out.is_file():
            sys.stderr.write(proc.stdout)
            sys.stderr.write(proc.stderr)
            raise RuntimeError(f"mmdc failed on {src.name}")
        print(f"rendered {out.relative_to(HERE)} ({out.stat().st_size:,} bytes)")
        rendered.append(out)
    return rendered


def extract_fences(md: str) -> tuple[str, list[str]]:
    """Pull fenced code out before pandoc sees it.

    Code goes straight into `lstlisting`, so the leanbox `literate` table renders
    the Lean glyphs and pandoc never gets a chance to escape or highlight them.
    """
    blocks: list[str] = []

    def take(match: re.Match[str]) -> str:
        blocks.append(match.group(1).rstrip("\n"))
        return PLACEHOLDER.format(len(blocks) - 1)

    return FENCE_RE.sub(take, md), blocks


def splice_fences(latex: str, blocks: list[str]) -> str:
    for i, code in enumerate(blocks):
        listing = "\\begin{lstlisting}\n" + code + "\n\\end{lstlisting}"
        token = PLACEHOLDER.format(i)
        if token not in latex:
            raise RuntimeError(f"code placeholder {i} vanished during conversion")
        latex = latex.replace(token, listing)
    return latex


def pandoc(markdown: str, shift: bool) -> str:
    cmd = [
        "pandoc",
        "-f",
        "markdown+tex_math_dollars+raw_tex+smart",
        "-t",
        "latex",
        "--wrap=preserve",
    ]
    if shift:
        cmd.append("--shift-heading-level-by=-1")
    proc = subprocess.run(cmd, input=markdown, text=True, capture_output=True, check=False)
    if proc.returncode != 0:
        sys.stderr.write(proc.stderr)
        raise RuntimeError("pandoc failed")
    return proc.stdout


def split_front_matter(md: str) -> tuple[str, str, str]:
    """Return (title_md, abstract_md, body_md)."""
    lines = md.splitlines()
    title = ""
    front: list[str] = []
    body_start = 0
    for i, line in enumerate(lines):
        if line.startswith("# ") and not title:
            title = line[2:].strip()
            continue
        if line.strip() == "---":
            body_start = i + 1
            break
        front.append(line)
    abstract = "\n".join(front).strip()
    # Inside an `abstract` environment the run-in "Abstract." label is redundant.
    abstract = re.sub(r"^\*\*Abstract\.\*\*\s*", "", abstract)
    body = "\n".join(lines[body_start:]).lstrip("\n")
    return title, abstract, body


def break_texttt_paths(latex: str) -> str:
    """Allow line breaks after `/` in \\texttt paths."""

    def fix(match: re.Match[str]) -> str:
        inner = match.group(1)
        if "/" not in inner:
            return match.group(0)
        return "\\texttt{" + inner.replace("/", "/\\allowbreak{}") + "}"

    return re.sub(r"\\texttt\{([^{}]*)\}", fix, latex)


def tidy(latex: str) -> str:
    latex = latex.replace("\\pandocbounded{", "{")
    latex = re.sub(r"\\tightlist\n", "", latex)
    return break_texttt_paths(latex)


def build_preamble() -> str:
    text = PREAMBLE.read_text(encoding="utf-8")
    if "literate=\n" not in text:
        raise RuntimeError("could not find the `literate=` table in the shared preamble")
    text = text.replace("literate=\n", "literate=\n" + EXTRA_LITERATE, 1)
    return text + EXTRA_UNICODECHAR + "\n\\providecommand{\\passthrough}[1]{#1}\n"


def build_title_page(title_tex: str, abstract_tex: str) -> str:
    return "\n".join(
        [
            r"\title{\textbf{" + title_tex + "}}",
            "",
            r"\author[1]{\textbf{" + AUTHOR + "}}",
            r"\affil[1]{ORCID: " + ORCID + "}",
            r"\affil[1]{" + COMPANY + "}",
            r"\affil[1]{\texttt{" + EMAIL + "}}",
            "",
            r"\date{\today}",
            "",
            r"\begin{document}",
            r"\maketitle",
            "",
            r"\begin{center}",
            r"  \small",
            r"  \textbf{Github:} \url{" + GITHUB_URL + r"}",
            r"\end{center}",
            "",
            r"\begin{abstract}",
            abstract_tex,
            r"\end{abstract}",
        ]
    )


def listing_block(path: Path, caption: str) -> str:
    rel = path.relative_to(HERE).as_posix()
    n_lines = len(path.read_text(encoding="utf-8").splitlines())
    return "\n".join(
        [
            f"\\subsection{{\\texttt{{{rel}}}}}",
            "",
            f"{caption} ({n_lines} lines).",
            "",
            r"\lstinputlisting{" + rel + "}",
        ]
    )


def build_appendix() -> str:
    return "\n".join(
        [
            r"\appendix",
            r"\section{Complete Lean source}",
            "",
            r"Checked by \texttt{lake build} against Lean 4 and Mathlib. "
            r"The development contains no \texttt{sorry}, no \texttt{admit}, "
            r"and no project-defined axiom. Palomar Comparator compares "
            r"\texttt{platonic\_solids\_3d}, \texttt{edges\_pos\_of\_regular}, "
            r"and \texttt{regular\_polychora\_classification}.",
            "",
            *[listing_block(path, caption) for path, caption in LEAN_MODULES],
        ]
    )


def main() -> int:
    render_mermaid_figures()
    title_md, abstract_md, body_md = split_front_matter(SRC.read_text(encoding="utf-8"))

    title_tex = tidy(pandoc(title_md, shift=False)).strip()
    abstract_tex = tidy(pandoc(abstract_md, shift=False)).strip()

    stripped_body, blocks = extract_fences(body_md)
    body_tex = splice_fences(tidy(pandoc(stripped_body, shift=True)), blocks)

    document = "\n".join(
        [
            build_preamble(),
            build_title_page(title_tex, abstract_tex),
            "",
            r"\tableofcontents",
            r"\newpage",
            "",
            body_tex,
            "",
            build_appendix(),
            "",
            r"\end{document}",
            "",
        ]
    )
    OUT_TEX.write_text(document, encoding="utf-8")
    print(f"wrote {OUT_TEX.name} ({OUT_TEX.stat().st_size:,} bytes)")

    proc = subprocess.run(
        ["latexmk", "-pdf", "-interaction=nonstopmode", "-halt-on-error", OUT_TEX.name],
        cwd=HERE,
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
        check=False,
    )
    if proc.returncode != 0 or not OUT_PDF.is_file():
        log = OUT_TEX.with_suffix(".log")
        sys.stderr.write(proc.stdout[-2000:])
        if log.is_file():
            sys.stderr.write("\n--- tail of LaTeX log ---\n")
            sys.stderr.write("\n".join(log.read_text(errors="replace").splitlines()[-40:]))
        return 1

    pages = subprocess.run(
        ["pdfinfo", OUT_PDF.name], cwd=HERE, capture_output=True, text=True, check=False
    ).stdout
    n_pages = next((l.split()[1] for l in pages.splitlines() if l.startswith("Pages:")), "?")
    print(f"wrote {OUT_PDF.name} ({OUT_PDF.stat().st_size:,} bytes, {n_pages} pages)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
