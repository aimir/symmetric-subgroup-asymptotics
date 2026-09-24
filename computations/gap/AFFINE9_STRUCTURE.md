# Structural coverage of two affine-nine blocks

This package exhausts the actual transitive actions with two blocks of size
nine and primitive affine local action. It identifies them with the shared
98-action alphabet used by the degree-eighteen normal and character data.
The [schema](../../certificates/schema/affine9_structure.md) states the precise
coverage argument, all retained witnesses and the GAP computational boundary.

From the publication root, with Python 3 and GAP 4.13.1:

```sh
python3 computations/gap/affine9_structure.py export --gap-command '/path/to/sage --gap'
python3 computations/gap/affine9_structure.py verify --gap-command '/path/to/sage --gap'
python3 computations/gap/affine9_structure_controls.py --gap-command '/path/to/sage --gap'
```

A direct GAP executable is also accepted. Use `--force` to replace an existing
output, `--data` to choose another certificate file, or `--alphabet` to choose
the corresponding literal action alphabet. Production and replay run in
separate GAP processes. The Python wrapper parses JSON as data, rejects GAP
errors even if the process exits with status zero, and requires the complete
semantic verdict. All build and replay inputs are inside the publication tree.

| Structural level | Retained witnesses |
|---|---|
| Natural GL(2,3) action | 16 subgroup representatives and 768 literal adjoining conjugators. |
| Primitive affine local actions | Seven irreducible stabilizers, with every actual local normal. |
| Goursat kernels | 75 square-inner outer-coset representatives; seven have automorphism order greater than two. |
| Block extensions | All 141 nonbase quotient involutions and their full preimages, reduced to 116 graph/extension certificates by literal wreath conjugators. |
| Nonsplit extensions | 36 certificates with no involutory swap outside their specified block kernel. |
| Physical actions | Literal S18 conjugators to all 98 pairwise nonconjugate shared targets. |

The committed [dataset](../../certificates/data/affine9_structure.json.gz) is a
single compressed JSON object of 7,395 bytes. Complete replay passes 5,179
assertions. Eight negative controls remove or alter adjoining edges,
irreducibility, local normals, outer cosets, quotient involutions, nonsplit
flags, target actions or automorphism orders; all are rejected.

The 116 certificates overlap on their 98 actual targets and must not be
counted as disjoint physical cases. This package changes no original action
weight. Its local normal-list completeness uses GAP `NormalSubgroups`; it does
not query an action catalogue. The separate normal/character package checks
all original normals after these actual action identifications.
