# Reproducible computations

These programs check finite witnesses and exact arithmetic used by the
[proof blueprint](../docs/blueprint/README.md). The complete binary menu checks
finite coverage using explicit closure witnesses. Other packages check the
nonbinary, primitive/rank and constructive block inputs; local fixtures have
their separately stated scopes. They do not prove the general capacity theorem or the
subgroup asymptotic. No formal
verification is claimed by the replay programs themselves. The separate
Lean witness export below supplies data for kernel checking. No CI is used.

Run from the repository root with Python 3.9 or later:

```sh
python3 computations/python/verify_degree16_quotient.py
python3 computations/python/verify_c1_incidence.py
python3 computations/python/verify_simultaneous_transport.py
python3 computations/python/critical_coefficients.py --check --max-degree 24
```

The four programs use only the Python standard library. Their paths do not
depend on the current working directory. The degree-16 verifier reads its
committed JSON by default and accepts an alternative certificate path;
the two incidence fixtures construct their finite inputs directly.

| Program | Expected mathematical verdict and limit |
|---|---|
| verify_degree16_quotient.py | The literal onto map has the exact kernel, proper subdirect image and stated invariants. No catalogue identification or complete-menu claim. |
| verify_c1_incidence.py | 238 finite assertions: S3/S4 oriented split marks and inverse-complement counts, a shared A4/C3 construction and a nonsplit C9 control. A necessary regression, not the universal c=1 theorem. |
| verify_simultaneous_transport.py | 979 finite assertions, including action multiplication: 36 distinct three-coordinate full-preimage transports preserve one joint quotient and positive C4 support. This does not check the asymptotic decoration cost. |
| critical_coefficients.py --check | Exact coefficient recurrence agrees with the separate orbit-colour sum through rank 20; Gaussian recurrence agrees with the product formula. Prints CSV containing exact benchmark L_n, not actual subgroup counts. |

For the complete binary witness and coverage replay:

```sh
python3 computations/gap/finite_menu.py verify
```

This checks every transitive binary action at degrees 2, 4, 8 and 16, every
normal outside the fixed base alphabet, the actual local witnesses and all
original symmetric normalizers. Action coverage uses Sylow/index-two closure;
normal coverage uses central-involution closure. The checker does not query
a group catalogue or call `NormalSubgroups`. Candidate production, bounded
controls and the precise scope are in [FINITE_MENU](gap/FINITE_MENU.md).

For the carrier normal profiles, master maps and exact rational inequalities:

```sh
python3 computations/python/verify_carrier_transitions.py
python3 computations/gap/run_carrier_checks.py
```

The [carrier package](gap/CARRIER_CHECKS.md) checks 14,008 literal kernels,
their full profiles and normal coverage, seven master quotient maps, exact
profile reductions and both rational cone certificates. Its group and numeric
checks supply different premises of the mixed-family estimate.

For the other finite theorem inputs:

```sh
python3 computations/gap/run_nonbinary_checks.py --catalogue
python3 computations/gap/primitive_rank.py verify
python3 computations/gap/pair_top_check.py --classifiers --constructors
python3 computations/python/pair_top_modules.py
python3 computations/python/pair_top_interfaces.py
python3 computations/gap/run_six_block.py verify
python3 computations/gap/run_four_block.py verify
python3 computations/gap/affine9_structure.py verify
python3 computations/gap/run_nonbinary_checks.py --scope affine9
python3 computations/gap/run_carrier_socket.py
python3 computations/python/verify_critical_quadratic.py
```

The [certificate inventory](../certificates/README.md) links each schema and
producer. Normal and module completeness, actual map verification and
original physical weights are explicit parts of these contracts. Primitive
and transitive catalogue inputs are pinned as documented. Nonbinary
`--catalogue` and pair-top `--classifiers` check catalogue-to-data
correspondence; they use the classifications, not prove them. The pair-top
`--constructors` rebuilds the 24/29/15 imprimitive domains and checks their
actual permutation conjugacies. Some full
replays take several minutes. No adjacent research file is needed.

For the separate local GAP chart and shared-source checks:

```sh
python3 computations/gap/run_local_checks.py
```

This discovers `gap` or `sage --gap` on PATH; `--gap-command` selects another
executable command without a shell. GAP 4.13.1 has been tested. Default checks
use literal permutations and require no catalogue identification: 454 local
chart assertions and 894 shared-source assertions. The optional catalogue
locator mode and degree-8 candidate generator are documented in the
[GAP package](gap/README.md).

The GAP runner rejects process errors and missing mathematical verdicts,
including GAP errors that otherwise leave a successful process exit status.
All Python checks also fail with a nonzero exit status on rejection. Finite
witness correctness and exhaustive action/normal coverage have separate checks,
as described in [FINITE_CERTIFICATES](../docs/blueprint/FINITE_CERTIFICATES.md).

No old research scripts, catalogues, logs or generated results outside this
directory tree are runtime inputs. These commands provide local computational reproduction with the documented
runtimes, not a kernel-checked proof.

## Literal Lean carrier witnesses

```sh
python3 computations/python/export_lean_carriers.py
python3 computations/python/export_lean_carriers.py --check
python3 computations/python/export_lean_carriers.py --chart 16T1086 --modular
python3 computations/python/export_lean_carriers.py --chart 16T1086 --modular --check
```

The exporter uses the committed binary menu to regenerate the four exceptional
carrier charts and their physical block words. It uses only the Python
standard library and resolves input paths relative to its own location.
The `--check` command compares the generated bytes without rewriting files.
The canonical degree-sixteen chart always consists of the modules in
`GeneratedCarrier16T1086/` and the two-import `BinaryExceptional16T1086.lean`
wrapper. Default and selected runs use the same modular output; `--modular`
remains accepted with `--chart 16T1086`. Selecting that chart leaves the
other three charts and physical-block files untouched.

Each row search stops before exceeding 1024 rows. The degree-sixteen alpha
graph has exactly 1024 rows; its beta graph and quotient have 256, its axis
has four, and its carrier kernel has one. Each degree-eight chart has at
most 64 rows in a table. The default run requires exactly these four original
charts. It reconstructs their generator transitions and words, without
restarting the action catalogue or normal-lift builds.

Check Lean modules serially with the bounded runner and current checked
imports, in this dependency order:

1. `FiniteGroupCertificates.lean`, then each degree-sixteen family's literal
   modules, `Data`, all `RowsNNN` modules, and `Certificate`. The families are
   `Alpha`, `Beta`, `Quotient`, `Axis`, and `CoverKernel`.
2. `AlphaMapsData` and `BetaMapsData`, their range/kernel `CheckNNN` modules,
   then `AlphaIdentification` and `BetaIdentification`, followed by the
   canonical `BinaryExceptional16T1086.lean` wrapper.
3. The three `BinaryExceptional8T16/8T20/8T21.lean` charts,
   `BinaryPermutationBlocks.lean`, and `BinaryCheckedTransport.lean`.
4. `BinaryExceptionalBlocks.lean`, `BinaryExceptional16Proper.lean`, then
   `BinaryExceptionalCarriers.lean`.

For example, after the preceding dependencies have been checked:

```sh
python3 -B scripts/check_lean.py SymmetricSubgroupAsymptotics/BinaryExceptionalCarriers.lean --log-dir ../lean-check-logs
```

The generated permutations, inverse rows, Cayley transitions, and generator
words are untrusted witnesses. Lean checks their equations and proves exact
quotient images, both original kernels, reversible transport with arbitrary
exterior groups, and the literal block projections. Balanced lookups and
finite proof chunks limit repeated kernel reduction; no native evaluation
oracle or external replay verdict is a proof premise. These four charts do
not establish complete finite-menu coverage.

## Structural roots and compact action certificates

```sh
python3 computations/python/export_lean_wreath_roots.py --check
python3 computations/python/export_lean_menu_cayley.py --check
python3 computations/python/export_lean_action_registry.py --width 8 --check
python3 computations/python/export_lean_generator_edges.py --check
```

The root exporter produces short two-way generator words for the original
degree-2, 4, 8 and 16 menu roots. Lean proves their Sylow property from a
faithful iterated-wreath action and its exact order. The second exporter
produces faithful numeric permutation codes, generator transitions and
well-founded parent paths. These give executable finite groups and exact
equivalences with the original generated permutation groups; no declared
group order or Python result is a proof premise. Its default output covers
the degree-2/4 actions and the order-1024 degree-16 exceptional source.
`--node ID` selects additional literal menu actions. Both read-only checks
reproduce committed source bytes and require only the Python standard library.

The degree-8 registry exporter checks every original-generator assignment and
all original-point child conjugacies, proving complete transitive binary
action coverage there. The generator-edge exporter demonstrates the compressed
method on every transitive index-two child of 16T1086: inverse-conjugated
target-generator membership and exact checked group orders force equality.
It uses packed numeric tables and small rejection witnesses. This covers
that action's children, not the whole degree-16 registry.

Action certificates, exhaustive registry coverage, and normal-state
acceptance are separate mathematical obligations. Generating a Cayley
certificate for an action does not discharge the latter two.

## Original Schreier-word action certificates

```sh
python3 -B computations/python/export_lean_schreier_actions.py --source b16_1086
python3 -B scripts/check_lean.py SymmetricSubgroupAsymptotics/GeneratedSchreierActions/Source16T1086.lean --log-dir ../lean-check-logs
```

The exporter selects one original action and bounds its word search, number
of assignments, and output size. Actual index-two subgroups are generated
by two Schreier words per original generator. Literal relations, preserved
point colourings, and two-way generator words certify every assignment.
No source order or source element table is a proof premise. The fixtures
`b2_1`, `b4_3`, `b16_1025`, `b16_1026`, and `b16_1082` through `b16_1101`
have passed kernel checking. The twenty-two degree-sixteen fixtures also have
checked common-registry bindings; complete degree-sixteen coverage requires
all 1,427 original sources and their bindings.

To emit a selected degree-sixteen source and its common-family binding
with one bounded witness search, use `--with-source`:

```sh
python3 -B computations/python/export_lean_schreier_bindings.py --source b16_1087 --with-source --max-states 1024 --max-assignments 64 --max-word-length 256 --max-cache-states 65536 --max-cache-bytes 67108864
python3 -B computations/python/export_lean_schreier_bindings.py --source b16_1087 --with-source --check --max-states 1024 --max-assignments 64 --max-word-length 256 --max-cache-states 65536 --max-cache-bytes 67108864
```

Both Schreier exporters reuse forward searches for the exact ordered target
generators within one selected invocation. Resuming the same breadth-first
order preserves the shortest words; all Lean equations remain required.
`--max-states` limits each search. `--max-cache-states` and `--max-cache-bytes`
limit the aggregate retained cache, defaulting to 65,536 states and 64 MiB.
Exceeding a limit aborts before witness files are written; it is never treated
as nonmembership. The byte budget conservatively accounts for retained Python
objects, excludes interpreter and temporary storage, and is not an RSS cap.
A container resize can cross it by one insertion before the immediate abort.
Nothing is cached across invocations or serialized as a group table.

Both files are bounded before either is written; each replacement is
atomic. Check `Source16T1087.lean` and then `Binding16T1087.lean` separately
with the bounded runner. The exporter reports branch counts and witness
word sizes. This example retains all 64 assignments, including 32 rejected
by literal relations; the assignment type is explicit in each Boolean proof.
The checked common-family bindings at indices 891–912 form two canonical
leaves, `Bindings0891Count0011.lean` and `Bindings0902Count0011.lean`, and
their checked join `Bindings0891Count0022.lean`. A leaf is emitted with
`export_lean_schreier_assembly.py --slice 891 11 --receipt-dir ../lean-check-logs`
only after its complete local dependency closure has current successful
receipts. A larger slice instead imports its two checked halves; the join
above uses `--slice 891 22`. Two of 128 canonical leaves and one of 127 joins
are checked. The remaining leaves and joins are required before the final
`Complete16` theorem can be checked.

Lean checks use the [bounded runner](../scripts/check_lean.py), with already
checked imports in dependency order. Generated modules are ignored build
outputs; logs and receipts belong outside this repository. The legacy
parallel action-table and full normal-lift builds are disabled.

The common degree-sixteen generator data can be rebuilt in bounded pieces:

```sh
python3 -B computations/python/export_lean_action16_data_chunks.py --chunk 0
python3 -B scripts/check_lean.py SymmetricSubgroupAsymptotics/GeneratedAction16/DataChunk000.lean --log-dir ../lean-check-logs
```

Each selected chunk contains at most32 original generator tuples. Check each
chunk serially. The explicit `--assemble --receipt-dir ../lean-check-logs`
mode replaces `Data.lean` only after every chunk matches its generator and
has a successful current check receipt. Then check `Data.lean` itself with
the same bounded runner. The common family indices, generator names and
action expression remain unchanged. These are data definitions, not an
action-coverage proof.

## Original degree-eight normal-state certificates

```sh
python3 computations/python/export_lean_normal_registry.py --check
python3 computations/python/export_lean_pair_frames.py --check
python3 computations/python/export_lean_pair_local.py --check
python3 computations/python/export_lean_pair_installed.py --check
python3 computations/python/export_lean_normal_characters.py --check
python3 computations/python/export_lean_finite_entry8.py --check
python3 -B scripts/check_lean.py SymmetricSubgroupAsymptotics/BinaryFiniteEntryCoverage8.lean --log-dir ../lean-check-logs
```

These standard-library exporters reproduce all 203 original nonbase normal
states in degree eight and their complete finite branches: 190 physical
pair certificates, 10 central-involution character criteria and three
transport charts. The kernel checks both exhaustion and each original
binding. The pair certificate retains the literal central cut, complete
fixed preimage, faithful quotient cover and physical width. The character
criterion checks the actual quotient's central involutions and exact integer
gap; the analytic character estimate is a separate theorem. The finite
coverage theorem keeps the eight base action indices explicit.

## Zero-ternary induced frames

The [frame package](frames/README.md) checks every literal induced frame,
all 812 binary invariant submodules, and the 38 odd-subgroup/normalizer
witnesses. Its separate constructors establish the bounded imprimitive
coverage; primitive completeness uses the stated classification input.

```sh
python3 computations/frames/run_frames.py
python3 computations/frames/negative_controls.py
```

The negative controls require that an omitted invariant module and a false
fixed-space witness are rejected. They operate on temporary copies.
