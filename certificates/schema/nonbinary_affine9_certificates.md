# Two affine nine-point blocks: literal normal and character data

The alphabet `../data/nonbinary_affine9_actions.json` contains 98 original
faithful transitive actions on 18 points, indexed `18A1` through `18A98`.
These are construction indices, **not** transitive-catalogue numbers. The
scope is a specified system of two nine-point blocks whose exact local
component is primitive affine. It is not the entire degree-18 catalogue.

The separate [structural certificate](affine9_structure.md) proves coverage
of this scope by local matrix subgroup closure, all Goursat graphs, every
permitted swap lift, and actual permutation conjugacies to this alphabet.
The character package does not infer that coverage from the number 98.

Each alphabet entry has `construction_index`, its literal degree-18
`generators`, `order`, complete original `normalizer_generators` and
`normalizer_order` in the symmetric group on 18 points, and `normal_count`.
Every entry has family `mixed`.

The compressed stream `../data/nonbinary_affine9_normals.jsonl.gz` has one
line per alphabet entry, in that order. Its class representatives, exact
cyclotomic character values, original normal kernels and join witnesses use
the [nonbinary certificate schema](nonbinary_certificates.md), with
permutation arrays of length 18. There are 1,823 literal normal entries.
Each has one fixed actual irreducible-character tuple whose kernel
intersection is precisely that original normal. The width-18 predicate is

\[
3^{64l}5^{64t}\le 2^{429},\qquad 429=24\cdot18-3.
\]

All supplied tuples in fact have `3^l 5^t <= 81`. Empty tuples occur only at
the whole normal subgroup. General slots are irreducibles; designated linear
slots are checked to have degree one. No character-table ordering, abstract
quotient isomorphism label, or numerical normal count supplies the witness.

As in degree 16, completeness of each literal normal list follows from all
conjugacy-class normal closures and closure under all joins with those
closures. The verifier does not call `NormalSubgroups`. Original actions and
their normalizers are retained even when two quotients are isomorphic.

Run the entire character/normal package from the repository root:

```sh
python3 computations/gap/run_nonbinary_checks.py --scope affine9 --gap-command 'sage --gap'
```

Regeneration, which may use `NormalSubgroups`, is separate:

```sh
python3 computations/gap/run_nonbinary_checks.py --scope affine9 --gap-command 'sage --gap' \
  --produce --data /tmp/nonbinary-affine9-regenerated.jsonl.gz
```

`--catalogue` is intentionally unavailable for this scope. The structural
certificate and the mixed-character counting lemma supply distinct inputs:
the former identifies all original actions in scope, while this package
checks the latter's literal finite hypotheses on every normal quotient.
