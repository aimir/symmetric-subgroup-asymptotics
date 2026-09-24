# Binary frames with zero ternary kernel

This is a standalone finite certificate package for the manuscript's
`lem:finite-zero-frames`. It verifies actual group actions and literal
stabilizer kernels, rather than inferring frame existence from group orders.
No file outside this directory is read, apart from GAP's declared group
library. Python uses only its standard library.

Run all focused checks from any directory:

```sh
python3 /path/to/symmetric-subgroup-asymptotics/computations/frames/run_frames.py --gap-command '/path/to/sage --gap'
```

Plain GAP on `PATH` is also detected. The four selectable parts are `all`,
`modules8`, `groups8`, and `groups16`. The wrapper rejects errors, warnings,
missing completion messages, timeouts, and nonzero exits. The finite
arithmetic checker does not use Python's disableable `assert` statement.

## Exact scope

* On eight blocks, 24 actual nonbinary transitive tops are used: 17 constructed
  imprimitive actions and the seven primitive actions. Every literal normal
  subgroup contributes to the calculation of the top's binary relative
  rank. Every stabilizer kernel with quotient C3 or S3 is retained, giving
  30 frames on 20 tops. The bound is `z2*(T) <= 2` for **all 24** tops,
  including the four tops having no frame.
* The 30 binary modules have dimension 16. Their 812 invariant submodules
  are independently checked by enumerating every vector orbit, forming
  every cyclic submodule, and checking closure under its sum with every
  listed submodule. This proves completeness of the module list. There are
  21,892 vector orbits and 39,449 cyclic-sum cells. All module head maxima
  are at most two.
* On sixteen blocks, the 29 constructed degree-sixteen tops each have one
  eligible stabilizer kernel. Each record supplies an actual Sylow
  three-subgroup and a binary element of its normalizer. The fixed space
  under this pair, plus the complete top relative rank, is at most ten.
* All 22 primitive degree-sixteen candidates are checked, including the
  ineligible ones. Their nine eligible literal frames on seven tops supply
  actual odd-subgroup witnesses and satisfy the same bound ten.
* The complete normal menus and Sylow-three orbit patterns of all seven
  primitive degree-eight local components are verified separately. These
  are used by the manuscript's two-block Goursat argument.

These finite results do **not** enumerate degree-32 or degree-64 affine
extensions. The manuscript's frame-extremum and section arguments handle
every proper or zero translation kernel and every nonsplit extension.
They also provide the nontrivial-socle bounds needed in addition to the
central binary type checked here.

## Classification premises

The primitive groups are the full degree-eight and degree-sixteen slices
of the PrimGrp library, used under its published classification premise.
The reference producer used GAP 4.13.1 and PrimGrp 3.4.4. The scripts check
the complete slice sizes, actual orders, local maps, and normal ranks;
they do not claim that a successful computation proves the primitive
classification. See the [PrimGrp documentation](https://gap-packages.github.io/primgrp/doc/chap1.html)
and the manuscript's classification references.

The 17 imprimitive eight-point tops are produced by the complete
two-four-block Goursat/swap constructions and the complete binary
four-block lift constructions. Their union has exactly three overlaps.
The manuscript supplies these structural completeness arguments.

`construct_tops16.g` gives the constructive completeness check for the 29
degree-sixteen tops. It first proves completeness of the eleven subgroup
classes of S4 by closure under adjoining every element. It then checks
every stabilizer map, both induced local frames, every invariant kernel
by cyclic extension, and every complement class by the exact linear
cocycle count. Its original extensions include nonsplit groups.

## Data and independent bindings

`frames8.json` contains the generator matrices and all module bases.
`bindings8.g` supplies the literal top groups, local epimorphisms, coset
representatives, induced permutation generators, and binary basis tying
each matrix to its actual action. `groups8` reconstructs each induced
frame and checks every conjugation matrix entry. `modules8` then proves
the module enumeration complete using independent binary linear algebra.

`tops16.g` supplies the 29 literal top actions. `frames16.g` contains the
38 literal stabilizer kernels, their **actual odd subgroups**, their
normalizer elements where used, and the exact numerical rows. `groups16`
reconstructs every induced frame, recomputes all top normal ranks, proves
stabilizer-kernel coverage, and verifies each supplied witness. It does
not discover a more favorable witness in place of a supplied one.

The detailed encodings are in `SCHEMA.md`. No historical source filename
is needed to interpret or execute these files.

## Reproduction

From this directory, the two finite producers are:

```sh
gap -q -T produce_frames8.g
gap -q -T produce_frames16.g
```

They replace their corresponding data files. This is deliberate producer
mode; the default checker never edits data. To reconstruct the 29 tops,
run `gap -q -T construct_tops16.g`; it writes `tops16_generated.g` so that
the committed input is preserved. The generated class representatives
may differ within their actual symmetric-group conjugacy classes.

The [finite manifest](../../certificates/manifests/finite_witnesses.json)
binds the supplied data and programs. A hash identifies bytes; the explicit
algorithms and mathematical coverage arguments establish their stated scope.
