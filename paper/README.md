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

The exact target and normalization are also recorded in [SPEC.md](../SPEC.md).
Preparation notes and the manuscript reconstruction record are maintained
outside this publication tree.
