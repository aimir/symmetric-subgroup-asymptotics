# Four binary blocks with A4 or S4 top

The [data](../data/four_block.json.gz) retain ten actual actions on eight
points, all 72 literal normal subgroups, original symmetric normalizers,
irreducible kernel/degree pairs and five actual central quotient maps.
Permutations are one-based image lists; map images follow the original source
generator order. Distinct normals with isomorphic quotients remain distinct.

The [checker](../../computations/gap/four_block.g) reconstructs the complete
classification directly. It adjoins all vectors to generate the 67 subspaces
of the binary base C2^4. For each of the two explicit top actions, the only
invariant subspaces are zero, the constant line C, the augmentation subspace
and the full base. For each of these it tries every pair of base corrections
to the two fixed top generators. Every subgroup projecting onto that top
contains lifts of those generators; together with its kernel these generate
the subgroup. Thus the enumeration is exhaustive. Translation conjugacy
reduces the lift lists, and actual S8 conjugacy verifies that the ten
transitive representatives are distinct. Replay matches each data action to
its constructed physical class and checks its original normalizer.

All normal subgroups are reconstructed as intersections of irreducible
character kernels. Completeness follows by decomposing the regular
representation of U/N: its inflated constituents have intersection of
kernels exactly N. The checker compares the entire literal normal lattice
and all irreducible kernel/degree pairs. It uses GAP's exact character and
finite-group algorithms, with no action catalogue or `NormalSubgroups` call.

For the five actions whose binary block kernel has order at least eight,
the checker verifies that the constant C2 is central, every nontrivial normal
contains it, and the original action admits a faithful irreducible character.
Each retained map is onto its explicitly constructed central quotient, with
kernel exactly C. The complete normal preimage count is also verified.
The four target models retain the same C3 action on both V4 factors, and
where appropriate the factor swap and/or simultaneous involution.
The repeated-F4 target has five distinct A4 quotient kernels and no faithful
irreducible character; those features are checked explicitly.

These are finite inputs to the character and repeated-head counting lemmas.
Their general source bounds, rank tails and weighted summations remain
mathematical arguments. The package has no claim about other block tops.

```sh
python3 computations/gap/run_four_block.py verify
python3 computations/gap/run_four_block.py export --output /tmp/four-block-candidate.json.gz
python3 computations/gap/run_four_block.py verify --input /tmp/four-block-candidate.json.gz
```

The driver accepts `--gap-command` and `--timeout` before the subcommand.
Export and verification are separate. All paths are release-local; data are
parsed as JSON and errors or missing complete verdicts reject the run.
