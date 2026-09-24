# Proof dependencies and reproducibility

The [literature reference](LITERATURE.md) states published mathematical inputs,
their source locators and applications. The
[mathematical dependency graph](claims.json) records the precise premise edges
and scopes, while the [blueprint](../docs/blueprint/README.md) explains them.
An edge is an implication dependency, not a proof certificate. Provenance
records connect:

* Exact theorem statements and dependencies, with the mathematical and
  finite inputs they consume.
* Precisely stated published mathematical inputs and primary references.
* Certificate schemas, generator/verifier versions, commands and input/output
  digests needed to reproduce the final computational claims.

Reproduction commands use a clean checkout and documented dependencies,
without requiring the original research workspace.

The [finite witness manifest](../certificates/manifests/finite_witnesses.json)
binds the selected binary, carrier, nonbinary, rank, pair-top and constructive
block data, their schemas and checker sources. Its counts and digests
identify the supplied artifacts; the documented replay checks, classification
premises and mathematical coverage arguments determine their validity. See
the [certificate inventory](../certificates/README.md) for each finite scope.
