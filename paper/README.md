# Manuscript

Build the manuscript from any working directory with Python 3 and a local
TeX distribution providing `latexmk`, pdfLaTeX, and BibTeX:

```sh
python3 /path/to/symmetric-subgroup-asymptotics/scripts/build_paper.py
```

The PDF is written to `paper/main.pdf`. Intermediate TeX files use a temporary
directory. Use `--output /path/to/paper.pdf` to choose a different output and
`--build-dir /path/outside/the/publication/tree` to retain the build log.
There is no network step or CI workflow.
The build stages TeX sources outside the publication tree, so stale auxiliary
files beside the originals cannot shadow its bibliography or references.

`main.tex` assembles the mathematical sections and the bibliography. The
argument proves the critical-family formula, complete binary recurrence,
nonbinary action exhaustion, packet and marker bounds, and the final ordinary
counting inequality. It concludes with exponential relative error against the
exact coefficient benchmark, a saddle-point formula with relative error
`O(1/n)`, and an elementary expansion with four residue-class constants.

The proof retains its published group-theoretic inputs and explicitly scoped
finite certificates. The [reading guide](../docs/blueprint/MANUSCRIPT_ROUTE.md)
describes how the parts fit together. The manuscript is a mathematical proof
draft; the computational checks are not formal verification.

The [final formal exports](../formal/README.md) now construct degree-two
coverage, the four-pair source, marked-C₄ encodings, affine consumers, and
quantitative socle profiles internally. Their explicit remaining mathematical
inputs are the published theorems and structural classifications listed in
that README. The canonical seven-input exports omit ordinary primitive normal
generation, simple two-generation and primitive composition length. Their needed relative-head, chief-weight, affine-source and automorphism estimates follow from actual orders, original Clifford data and the retained simple-index inequalities. The current source/object and final-target axiom audits are
described precisely in the formal README.
This verifies the three targets relative to those explicit published inputs;
it does not formalize the retained literature itself. The optional CFSG
backend now proves the weak labelled transitive-count input internally.
Its successor T1 endpoint retains three published bundles, pinned CFSG,
and two restricted model callbacks. The shared Y-derived and original J1
binary-frame proofs reduce the GoodSylow callback to 14 sporadic cases;
the numerical callback retains 21. A CFSG-only proof of T1 remains open.

The exact target and normalization are also recorded in [SPEC.md](../SPEC.md).
Preparation notes and the manuscript reconstruction record are maintained
outside this publication tree.
