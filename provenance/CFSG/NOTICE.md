# License and provenance notices

Original implementation and documentation in this repository are provided under
the Apache License, Version 2.0; see [LICENSES/Apache-2.0.txt](LICENSES/Apache-2.0.txt).
This does not relicense external works, mathematical databases, or cited papers.

Mathlib is an external pinned dependency under Apache-2.0. Each transitive
dependency retains its own upstream license; the exact source revisions are in
`lake-manifest.json`. No dependency checkout or compiled artifact is vendored.

`CFSG/Models/Mathieu22.lean` adapts the two permutation declarations by Kenta,
copyright 2026, from KitaKen1/finite-simple-groups-lean at
`7f09e33a9ceef6b59ce03e34cd4f0558c763e325`. The copyright and license notice is
retained in the file; no upstream proof or native certificate is silently imported.

The literal relators and matrix entries in `Models/Presentations` and
`Models/MatrixGroups` are mathematical data transcribed from the **ATLAS of Finite
Group Representations**, prepared by R. Wilson, P. Walsh, J. Tripp, I. Suleiman,
R. Parker, S. Norton, S. Nickerson, S. Linton, J. Bray and R. Abbott.
[ATLAS](https://brauer.maths.qmul.ac.uk/Atlas/); exact data files and hashes are in
`provenance/atlas.json`. This repository does not redistribute their Magma
programs, HTML pages, or prose. The new parser and Lean definitions are original.

No explicit license for those external ATLAS **data files** was found in the
inspected pages. The GAP AtlasRep **interface package** is GPL-3.0-or-later, but
that was not taken to establish a license for all separately hosted database
files. Accordingly no blanket Apache/GPL license is asserted over the external
data. Clarifying the database's reuse terms is an outstanding provenance issue
for redistribution; the attribution and exact source pins are retained here.

Höhn's ATLAS at `3c4e29f12a48132ee9ce7b11e01eb1dff766331e` uses the custom
ATLAS Research and Attribution License 1.0, including noncommercial restrictions.
It was inspected, not copied or added as a dependency. Formal Abstracts (MIT)
and Qiuzhen CFSG (Apache-2.0) were likewise inspected without adopting code.
Their pinned revisions, configuration hashes and license hashes are recorded in
`provenance/projects.json`; findings are in `docs/INVENTORY.md`.

The Serre/Chevalley, Suzuki, and Y-group mathematical definitions are original
formal transcriptions of formulas with source locators in the audits. Cited
articles and books retain their original copyrights and are not redistributed.
