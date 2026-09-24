# Precise asymptotics for subgroups of the symmetric group

Mathematical statements, proof exposition, finite certificates and reproducible
computations for the number of subgroups of the symmetric group.

Read the [statement and normalization](SPEC.md),
[manuscript and local build instructions](paper/README.md),
[mathematical blueprint](docs/blueprint/README.md),
[external mathematical inputs](provenance/LITERATURE.md) and
[assumptions and evidence boundary](ASSUMPTIONS.md).

## Contents

| Path | Content |
|---|---|
| paper/ | Manuscript sources, appendices, bibliography and figures. |
| formal/ | Pinned Lean project, [formal theorem targets and proved foundations](formal/README.md). |
| certificates/ | Literal finite witnesses and data contracts. |
| computations/ | GAP/Python witness producers, independent checks and exact arithmetic. |
| scripts/ | Local build and reproduction commands. |
| docs/blueprint/ | Mathematical interfaces and their dependency structure. |
| provenance/ | Mathematical sources and certificate provenance. |

The [manuscript reading guide](docs/blueprint/MANUSCRIPT_ROUTE.md) follows the
complete argument through its local estimates, exhaustive partition and final
boundedness inductions. The blueprint describes exact counting, the critical model, capacity and fusion,
the c=1 application, binary control, global assembly and analytic corollaries.
It supplies mathematical interfaces rather than a self-contained proof of the
main theorem.

The [finite package](certificates/README.md) contains the small-width binary
menu, carrier profiles, nonbinary degree-16 witnesses, primitive/rank inputs,
count-twelve and count-sixteen pair-top certificates, constructive four- and
six-block classifications, two-affine-nine-block witnesses, and zero-ternary
induced-frame certificates. It retains
literal actions, normal kernels, original weights and actual quotient maps.
Other computations check
shared-C3 moments, inverse-complement incidence, proper-subdirect transport
and exact critical coefficients. Run the [documented local commands](computations/README.md)
from this tree with the stated dependencies; no research-workspace files are
runtime inputs.

The binary menu couples literal witness checks to two mathematical closure
arguments establishing coverage at degrees 2, 4, 8 and 16. The local chart
fixtures have a narrower scope. These computations do not establish the
general asymptotic theorem or formal verification. A benchmark value produced
by the coefficient program is not an actual subgroup count.
