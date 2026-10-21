# Pinned classification statement

The concrete classification statement is copied from `cfsgStatement` commit
`25507f8795f2e499b392f3312a576538e1c5ef78` into
`formal/SymmetricSubgroupAsymptotics/External/CFSG/`, with its root module at
`External/CFSG.lean`. Imports beginning with `CFSG` are prefixed by
`SymmetricSubgroupAsymptotics.External.`; the build-time axiom audit's module
filter receives the same prefix. Mathematical declarations retain
their upstream namespace and definitions. The source is frozen independently
of subsequent development of the originating repository.

The upstream Lean and mathlib revisions coincide with this project's pins.
`CFSG.CFSGClassification` is an explicit proposition supplied as a theorem
hypothesis, not an axiom declaration or a proof of classification. It asserts
that every finite simple group is isomorphic to an indexed concrete model.
It asserts no order, simplicity, generation, automorphism or subgroup-index
property of all models. Such properties require separate downstream proofs.

Original implementation is Apache-2.0; the upstream license and complete notice
are preserved in [CFSG/Apache-2.0.txt](CFSG/Apache-2.0.txt) and
[CFSG/NOTICE.md](CFSG/NOTICE.md). Exact original ATLAS data locators and hashes
are retained in [CFSG/atlas.json](CFSG/atlas.json). The upstream notice records
the distinct provenance of those mathematical data and the adapted M22
permutations; it does not assert a blanket license over external databases.

The definition of the classification proposition is independently auditable
in `External/CFSG/Classification.lean`. Exhaustiveness is the intended
external mathematical hypothesis. Merely defining the listed group models
does not prove their conventional identifications or any downstream theorem.
