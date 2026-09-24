# Carrier finite checks

The carrier certificate is described in
[its schema](../../certificates/schema/carrier_transitions.md). Run these
commands from the project root. Python 3 uses only the standard library;
the group checks require GAP. `--gap-command 'sage --gap'` also works when
GAP is supplied by SageMath.
The wrapper enforces a two-hour GAP timeout by default; use `--timeout`
to specify another positive number of seconds.

Exact rational menu reductions and two-cone inequality:

```sh
python3 computations/python/verify_carrier_transitions.py
```

Literal master maps, original normalizers, every supplied kernel/profile,
and normal-list completeness:

```sh
python3 computations/gap/run_carrier_checks.py
```

For just the seven maps and original action weights:

```sh
python3 computations/gap/run_carrier_checks.py --maps-only
```

The full run checks all 14,008 kernels. It constructs actions from the
supplied permutation generators and checks normal-list coverage through
central involution extensions. It does not query a transitive-group catalogue
or call `NormalSubgroups`. Runtime depends on GAP's finite-group algorithms;
the map-only check does not establish normal-profile coverage.

The separate producer can regenerate a candidate kernel certificate:

```sh
python3 computations/gap/run_carrier_checks.py --produce --normals /tmp/carrier_normals.jsonl.gz
python3 computations/gap/run_carrier_checks.py --normals /tmp/carrier_normals.jsonl.gz
```

Production uses `NormalSubgroups`; acceptance of the output still requires
the second command, which checks the explicit closure witnesses. The
numerical and group checkers have distinct responsibilities and both are
required. The producer's PASS output is not a verification result.
