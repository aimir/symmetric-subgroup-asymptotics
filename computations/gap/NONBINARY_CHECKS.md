# Degree-16 nonbinary finite verification

From the repository root:

```sh
python3 computations/gap/run_nonbinary_checks.py --gap-command 'sage --gap'
```

This verifies all 527 literal actions, original normalizer weights, 9,249
normal kernels, exact irreducible character tuples, and the central-head and
comparator quotient maps. It uses only the committed data and ordinary GAP
finite-group algorithms. It makes no catalogue query and does not enumerate
normal subgroups with `NormalSubgroups`.

The normal-list completeness proof is closure under the normal closures of
all conjugacy classes. See the [data schema](../../certificates/schema/nonbinary_certificates.md)
for the proof, exact cyclotomic representation, and map conventions.

To additionally verify correspondence with every entry of the pinned
TransGrp 3.6.5 degree-16 slice:

```sh
python3 computations/gap/run_nonbinary_checks.py --gap-command 'sage --gap' --catalogue
```

This checks all 1,954 indexed classes, the binary/nonbinary partition, and
permutation conjugacy of every nonbinary class to its committed original
action. It still **uses** the published classification as a premise. The
classification and the official catalogue correspondence are described in
[the literature inventory](../../provenance/LITERATURE.md).

Regeneration is deliberately separate:

```sh
python3 computations/gap/run_nonbinary_checks.py --gap-command 'sage --gap' \
  --produce --data /tmp/nonbinary-regenerated.jsonl.gz
```

The producer starts with the committed literal actions. It may call
`NormalSubgroups`, computes irreducible characters and least-cost fixed tuples,
constructs central-head or comparator maps, and emits every normal entry.
Character and subgroup orderings may change across GAP releases; the verifier
compares mathematical values, kernels and maps, rather than producer indices.
A regenerated file should be checked with `--data` before use.

`--actions 16T1071,16T1298` performs a clearly labelled partial run and never
prints the complete-pass marker. `--timeout` bounds the GAP process. Alternate
`--alphabet` files must have the committed action domain and are matched to
its actual permutation groups and original weights. Permutation rows and
all local indices are checked before GAP executes.

The finite results certify the local hypotheses of the mixed-character,
derived-quotient comparator, and repeated-head counting lemmas. Those analytic
lemmas, the published degree-16 classification, and GAP's exact finite-group
algorithms remain the stated mathematical and computational inputs. This
program does not verify a global recurrence, a terminal attachment, or a
classification in a different degree.

## Two affine nine-point blocks

The same exact character and normal-closure checker has a second explicitly
bounded scope:

```sh
python3 computations/gap/run_nonbinary_checks.py --scope affine9 --gap-command 'sage --gap'
```

It checks 98 original degree-18 actions and 1,823 normals, all by mixed
characters with threshold `3^(64*l) * 5^(64*t) <= 2^429`. These action indices
come from the separate Goursat/swap construction, not a degree-18 catalogue.
See the [affine-nine schema](../../certificates/schema/nonbinary_affine9_certificates.md)
and [structural checker](AFFINE9_STRUCTURE.md). Regeneration uses the same
command with `--produce --data /tmp/nonbinary-affine9-regenerated.jsonl.gz`.
