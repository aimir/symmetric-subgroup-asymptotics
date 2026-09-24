# Reproducible computations

These programs check finite witnesses and exact arithmetic used by the
[proof blueprint](../docs/blueprint/README.md). The complete binary menu checks
finite coverage using explicit closure witnesses. Other packages check the
nonbinary, primitive/rank and constructive block inputs; local fixtures have
their separately stated scopes. They do not prove the general capacity theorem or the
subgroup asymptotic. No formal
verification or CI is involved.

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
