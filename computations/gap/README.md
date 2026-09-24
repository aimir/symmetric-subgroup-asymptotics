# GAP checks

The [complete binary menu](FINITE_MENU.md) has its own exporter and checker,
including exhaustive action and normal-subgroup coverage at degrees 2, 4, 8
and 16. The local runner documented below checks the four exceptional quotient
charts and a common-source second-moment regression. That runner has no
complete-menu claim. Neither runner verifies the general weighted estimates
or performs formal verification. The separate
[carrier package](CARRIER_CHECKS.md) checks all master-action normal profiles
and the maps covering the original carrier colours. No research-workspace
file is read at runtime.

The other finite-input packages are documented in
[NONBINARY_CHECKS](NONBINARY_CHECKS.md), [PRIMITIVE_RANK](PRIMITIVE_RANK.md),
[pair-top checks](pair_top_checks.md), [SIX_BLOCK](SIX_BLOCK.md),
[the four-block schema](../../certificates/schema/four_block.md),
[AFFINE9_STRUCTURE](AFFINE9_STRUCTURE.md) and
[the carrier socket schema](../../certificates/schema/carrier_socket.md).
Their coverage and software boundaries are stated separately. The
[computation index](../README.md) lists the complete replay commands.

## Run

From the repository root:

```sh
python3 computations/gap/run_local_checks.py
```

Python 3.9+ is used only for JSON decoding, temporary GAP input and process
control. The runner uses `gap` from PATH, or `sage --gap` if that is available.
A command can be selected explicitly, without invoking a shell:

```sh
python3 computations/gap/run_local_checks.py --gap-command 'sage --gap'
```

Paths are resolved from the runner's location, so it also works from another
working directory. `--degree16 FILE` and `--degree8 FILE` select alternative
JSON inputs; `--timeout SECONDS` changes the default 120-second process limit.
Errors, syntax warnings, nonzero GAP exit status, and missing final PASS markers are
rejected. GAP sometimes exits successfully after a script error, so the exit
code alone is deliberately insufficient.

The default run does not call `TransitiveGroup`, `TransitiveIdentification`,
`SmallGroup` or `IdGroup`. Its input groups are literal permutations, and its
checks use GAP's group algorithms. This is a computational check; it does not
remove GAP itself from the software trust boundary.

Optional catalogue **locator** checks can be added:

```sh
python3 computations/gap/run_local_checks.py --catalogue-locators
```

This verifies that the supplied actions/quotients match their advertised
transgrp/SmallGroup identifiers. It is not a proof that any catalogue or list
of cases is complete. The default run needs no such identification.

## What is checked

`verify_local_charts.g` reads the existing
`certificates/data/degree16_quotient.json` and the new
`certificates/data/degree8_quotient_charts.json` through the runner.

* Degree16: literal source and image orders, transitivity, onto map, exact
  order 4 kernel, uniqueness of that normal order 4 axis, centre/Frattini/derived
  invariants, exponent/class, and the actual C4[4],D8[4],D8[4],D8[4] projections.
  The image remains the order 256 proper subdirect, not its order 2048 ambient
  product. A correlated exterior P x C2 is retained through a complete
  full-preimage inverse on 34 physical points.
* Degree8: three pairwise nonconjugate literal source actions of order 32,
  exact normal order 2 axes, and explicit maps from each source and the common
  order 64 degree 8 carrier onto the SAME order 16 quotient. The replacement
  kernel has order 4. All32 quotient automorphisms per source give96 correlated
  two-factor full-preimage checks.
* Both chart sizes keep the original physical degree. The degree 16 target has
  noncritical fraction1/4; the degree 8 carrier has fraction1, using its
  separately stated membership in the noncritical carrier alphabet.

`verify_shared_source_moment.g` is also run. It constructs A4->C3 using literal
permutations, enumerates subgroups of C3 x C3 x J **before** selecting graphs,
and then lifts through the two A4 covers. For J=C3,C3^2 the records are

```text
[e_Q(J), ordered onto-map pairs, pairs with full joint Q^2 image,
 total graph count over all subgroups of J]
[[2,4,0,4], [8,64,48,80]].
```

Thus the proper joint images are included. The64 and80 count different sets;
80 includes graphs over proper subgroups of C3^2. This fixture does not prove
the general graph-moment theorem or the complete c=1 theorem. It can also run
alone with `gap -q -T computations/gap/verify_shared_source_moment.g`.

## Degree8 data contract and optional producer

All permutations are one-based image lists. The top-level cover generators
act on1,...,8. Each chart contains source/kernel generators on1,...,8,
quotient generators on1,...,16, one `alpha_images` row per source generator,
one `beta_images` row per cover generator, and literal cover-kernel generators.
The quotient's regular degree16 representation is AUXILIARY: it is not a
replacement physical action or an additional block in the counting argument.
The quotient orders and kernel sizes are verified, not accepted from metadata.
Library locators are descriptive until the optional mode checks them.

The committed JSON is sufficient to run the verifier. To produce a fresh
candidate using GAP's transitive catalogue:

```sh
gap -q -T computations/gap/export_degree8_charts.g > candidate_degree8.json
python3 computations/gap/run_local_checks.py --degree8 candidate_degree8.json
```

The exporter is an untrusted, catalogue-dependent DATA PRODUCER. Its choices
of quotient generators/maps may differ across GAP versions; byte-for-byte
regeneration is not promised. Never overwrite the committed certificate merely
because export completed. Verify the candidate independently first. The
exporter does not produce complete action or normal-subgroup coverage evidence.

## Expected verdicts and tested runtime

The package has been run using GAP 4.13.1 through Sage. Default
checks pass 454 local-chart assertions and 894 shared-source assertions.
The optional locator mode passes459 local-chart assertions, using
transgrp 3.6.5, plus the same 894 shared-source assertions. Four negative inputs
are rejected: a malformed permutation, a well-formed non-onto cover map, an
incorrect degree16 kernel, and a duplicated degree8 action. These are local computational checks, not coverage or asymptotic proofs.

The standard-library Python degree16 checker is independent of these GAP
algebra checks. The mathematical contract in
`docs/blueprint/FINITE_CERTIFICATES.md` distinguishes local witness validity
from complete action and normal-subgroup coverage.
