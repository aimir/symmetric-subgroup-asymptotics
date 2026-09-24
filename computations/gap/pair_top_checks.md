# Pair-top finite checks

Run these commands from the repository root. Python uses only its standard
library. GAP 4.13.1 was used for the local replay; the optional classification
correspondence also needs the TransGrp and PrimGrp libraries.

```sh
python3 computations/python/pair_top_modules.py
python3 computations/gap/pair_top_check.py --constructors
python3 computations/python/pair_top_interfaces.py
```

A GAP or Sage executable is discovered on `PATH`. A Sage installation can also provide GAP with
`--gap-command '/usr/local/bin/sage --gap'`. The wrapper invokes it with
`-q -T`, rejects errors and incomplete output, and kills its process group
on timeout. `--timeout` is in seconds. A timeout is a failed replay.

All three commands are required for the complete finite interface check.
The Python module program reconstructs every invariant subspace and exact
Hom equation from the literal actions. The GAP program reconstructs every
normal as an intersection of actual irreducible kernels and verifies its
fixed character tuple. `--constructors` additionally rebuilds the complete
24-, 29-, and 15-action imprimitive domains and checks all 68 retained
permutation transporters. The interface program binds those records to the
same action, checks the retained averaging and pair maps, and evaluates the
exact integer predicates at original width 24 or 32.

Expected complete module totals are:

| Family | Actions | Invariant numerators | Simple intervals | Hom cells |
|---|---:|---:|---:|---:|
| Twelve-point | 301 | 5,044 | 8,483 | 10,960 |
| Paired eight-point | 24 | 170 | 169 | 361 |
| Zero-ternary sixteen-point | 29 | 812 | 1,659 | 1,624 |
| Two affine eight-point blocks | 15 | 140 | 146 | 399 |
| Primitive affine sixteen-point | 20 | 198 | 233 | 680 |
| Paired six-point | 2 | 12 | 14 | 24 |

The group replay checks all 4,623 literal normals: respectively 3,914, 147,
349, 95, 101, and 17 in those families. The paired eight-point module check
also verifies 4,479 common-product triples. Counts are regression checks;
the exhaustive vector and irreducible-kernel constructions supply the
completeness arguments.

To regenerate the two certificate streams and construction transporters
from the committed literal alphabet:

```sh
python3 computations/python/pair_top_modules.py --produce
python3 computations/gap/pair_top_check.py --constructors --produce
```

Producer mode overwrites only its specified output data. Use `--data` to
write elsewhere; `--construction-data` selects the construction transporter
file. Optional `--classifiers` checks the indexed degree-12 and
primitive degree-8/16 actions against their installed catalogue
representations. Default replay has no catalogue dependency. Catalogue
classification, the uniform block-structure reductions, and the universal
all-original-normal lifting theorems have the precise separate status
described in the [certificate schema](../../certificates/schema/pair_top_certificates.md).

The alphabet and both certificate streams contain literal mathematical
data, with no research-workspace imports. Each compressed stream uses one
record per action. Full normal subgroups are retained even when their
quotients are abstractly isomorphic. Auxiliary top degrees and compression
degrees never change an original action's physical width or weight.
