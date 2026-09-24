# Primitive and rank finite inputs

This package consolidates the finite primitive, transitive-rank and c=1 seams
used by the counting proof. It contains literal actions, normal subgroups,
composition series and actual maps, rather than historical scan logs.
The [schema](../../certificates/schema/primitive_rank.md) defines each field
and the classification/computational trust boundary.

From the publication root, use Python 3 and GAP 4.13.1 with PrimGrp 3.4.4 and
TransGrp 3.6.5:

```sh
python3 computations/gap/primitive_rank.py export --gap-command '/path/to/sage --gap'
python3 computations/gap/primitive_rank.py verify --gap-command '/path/to/sage --gap'
python3 computations/gap/primitive_rank_controls.py --gap-command '/path/to/sage --gap'
```

Use `--force` to regenerate an existing file; `--data` selects another output or
input. The normal command also works with a direct GAP executable. Production
and replay are separate processes. The wrapper rejects GAP error output even
when the executable exits with status zero; the final semantic verdict is
required. The control command deliberately changes witnesses and checks that
the verifier rejects them.

| Consumer | Retained finite input |
|---|---|
| Sharp first head | 7,259 transitive actions, plus 233 transitive-normal pairs at degrees 2,4,8. |
| Relative ternary equality and stability | All normal pairs in transitive degrees 6,9,12,18: 20,628 records. The c=1 degree-6/12/18 portion has 20,410 pairs; degree 9 adds 218. |
| Primitive relative head | 945 normal pairs in the 253 primitive actions through degree 33; this contains the earlier 2/9 and stability ranges. |
| Primitive composition | 336 actions through degree 44, plus four primitive degree-54 actions needed by the minimal-block argument. |
| First c=1 acceptance | Eleven actual structural witnesses; their high normal pairs are retained in the same rank records. |
| Nonsoluble degree-18 top | 91 actual semiregular witnesses and the same 521 normal-pair records. |
| Nonaffine primitive compression | Degrees 5–29: 116 simple-socle certificates; the four nonsimple-socle cases keep their separate analytic treatment. |
| Nonsoluble affine exceptions | Thirteen actions at degrees 8,16,27, with actual stabilizer composition chains. |

Rows overlap mathematically. Their counts must not be added as disjoint
physical subgroup families. No larger exploratory catalogue ranges or unused
minimal-degree optimizations are required by this package.

The committed [dataset](../../certificates/data/primitive_rank.jsonl.gz) contains
7,599 action records and 21,806 literal normals, plus its header and footer.
Complete replay checks 908 primitive composition factors and 322,693 assertions.
The negative control suite rejects nine altered certificates. These are checks
of the stated finite input package, with the classification and GAP trust
boundary documented in the schema.
