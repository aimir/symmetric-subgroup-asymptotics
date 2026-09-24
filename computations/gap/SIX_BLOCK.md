# Six-pair action certificates

From the publication repository root, with Python 3.9+ and GAP:

```sh
python3 computations/gap/run_six_block.py verify
```

Use `--gap-command 'sage --gap'` before `verify` if GAP is supplied by Sage.
The default timeout is 7,200 seconds; `--timeout` also precedes the mode.
The [schema](../../certificates/schema/six_block.md) gives the full mathematical
scope and both coverage arguments.

The supplied data have 56 S6 subgroup classes, 2,825 binary subspaces,
112 top/module interfaces,224 block certificates,182 physical actions and
2,476 literal normal records. The verifier reconstructs every retained
conjugator, normal join, character cover and exceptional quotient map.
It does not call a group catalogue, `NormalSubgroups`, `AllSubgroups`,
`ConjugacyClassesSubgroups` or `ComplementClassesRepresentatives`.

To generate and independently check a candidate:

```sh
python3 computations/gap/run_six_block.py export --output candidate_six_block.json.gz
python3 computations/gap/run_six_block.py verify --input candidate_six_block.json.gz
```

The producer may use subgroup and complement enumeration. The verifier uses
explicit closure witnesses and independent relator cocycle dimensions for
completeness. Candidate generation is not a verification verdict. Existing
outputs require `--force`. Data and code use no research-workspace inputs.
