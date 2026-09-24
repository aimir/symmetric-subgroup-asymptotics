# Finite certificates

Each certificate here supplies a concrete witness needed by the final proof.
Computational checks and formal proofs provide different kinds of evidence.

## Complete binary menu and base alphabet

The [complete menu](data/binary_menu.jsonl.gz) supplies literal normal-subgroup
witnesses outside the [fixed seventeen-colour base alphabet](data/base_alphabet.json)
at degrees 2, 4, 8 and 16. It retains original action normalizers, central
cuts, actual faithful quotient maps, whole-centre character checks and the
four exceptional replacement maps.

Action coverage starts at explicit Sylow wreath groups and checks every
transitive index-two child. Normal coverage starts at the identity and checks
every central-involution extension in each quotient. The
[schema](schema/binary_menu.md) proves why these two closure checks suffice;
replay does not query a group catalogue or call `NormalSubgroups`.

    python3 computations/gap/finite_menu.py verify

The [export/replay documentation](../computations/gap/FINITE_MENU.md) also gives
candidate generation and focused controls. GAP's group algorithms remain in
the computational trust boundary. The general source-counting and weighted
mixture theorems are separate mathematical inputs.

## Carrier profiles and transition inequalities

The [carrier certificate](schema/carrier_transitions.md) retains all 14,008
literal normal kernels of the eight master actions, seven generator-image
quotient maps covering the original degree-eight colours, exact profile
reductions and rational cone certificates. It supplies the finite inputs
inside the base alphabet, which the binary entry menu handles separately.

    python3 computations/python/verify_carrier_transitions.py
    python3 computations/gap/run_carrier_checks.py

The group replay checks all normal kernels through central-involution closure;
the numerical replay checks the profile domination and quadratic inequalities
with exact rational arithmetic. Both are required. See
[execution instructions](../computations/gap/CARRIER_CHECKS.md).

## Nonbinary, rank and constructive block inputs

These packages have separate action-coverage premises and share data where
the same finite action is used by several bounds. The schemas distinguish
mathematical classification, literal action correspondence, complete normal
or module lattices, and the resulting inequalities.

| Package | Retained finite scope | Contract and commands |
|---|---|---|
| Nonbinary degree 16 | 527 actual actions and 9,249 literal normals; mixed characters, comparator maps and repeated-head maps | [Schema](schema/nonbinary_certificates.md), [GAP commands](../computations/gap/NONBINARY_CHECKS.md) |
| Primitive and relative rank | 7,599 action records and 21,806 normal rows across overlapping first-head, primitive and c=1 ranges | [Schema](schema/primitive_rank.md), [GAP commands](../computations/gap/PRIMITIVE_RANK.md) |
| Count-twelve/count-sixteen pair tops | 391 retained action records, complete binary module lattices and 4,623 all-normal menus; original physical widths retained | [Schema](schema/pair_top_certificates.md), [commands](../computations/gap/pair_top_checks.md) |
| Six binary blocks | 16 transitive tops, 112 invariant interfaces, 224 block certificates, 182 physical actions and 2,476 normals | [Schema](schema/six_block.md), [GAP commands](../computations/gap/SIX_BLOCK.md) |
| Four binary blocks, A4/S4 top | Ten physical actions, 72 normals and five central quotient maps | [Schema and commands](schema/four_block.md) |
| Two affine nine-point blocks | 75 graphs, 116 graph/swap certificates and 98 physical actions; all 1,823 normal/character entries | [Structural schema](schema/affine9_structure.md), [character schema](schema/nonbinary_affine9_certificates.md), [commands](../computations/gap/AFFINE9_STRUCTURE.md) |
| Zero-ternary induced frames | 30 binary frames and 812 complete module lattices; 38 literal odd-subgroup/normalizer witnesses on sixteen-block tops | [Schema](../computations/frames/SCHEMA.md), [commands and coverage](../computations/frames/README.md) |
| Narrow C4 socket and quadratic constants | All twelve carrier Bockstein profiles, exact C4 pullbacks and the critical isometry orders | [Schema and commands](schema/carrier_socket.md) |

The first two packages use the pinned published classifications. The pair-top
package combines classification inputs with constructive reductions stated in
its schema. The four-block, six-block and affine-nine construction checkers
supply their own bounded coverage evidence. Exact GAP character, conjugacy,
normalizer and finite-group calculations remain computational dependencies.
In particular, the primitive/rank replay uses GAP's normal-subgroup enumeration;
its trust boundary differs from the binary closure checker.

The zero-ternary frame package binds its matrices to literal induced actions.
An independent Python cyclic-sum closure proves the eight-block module lists
complete. The sixteen-block witnesses contain actual odd subgroups and
normalizer elements. Primitive-top completeness uses the declared PrimGrp
classification; the 29 imprimitive tops have a separate constructive replay.
The manuscript's frame theorem handles arbitrary translation kernels and
extensions above those frames.

The [finite manifest](manifests/finite_witnesses.json) binds the data, schemas
and checker bytes and lists replay commands. A digest is a file binding,
not mathematical evidence of acceptance or coverage.

## Degree-16 quotient chart

The [literal data](data/degree16_quotient.json) define groups U, N and P by
permutations on the same sixteen points, and a proposed map pi:U->P by its
values on the source generators. The data verify:

* U is transitive, |U|=1024, and pi is surjective with exact kernel N of order 4.
* P has order 256 and four specified orbits of length four. Its projection
  groups are the regular C4 action and three natural D8 actions.
* Thus P is a proper subdirect subgroup of C4 x D8^3, whose full product has
  order 2048. Its actual joint relations remain in the supplied permutations.
* The degree is unchanged and the C4 orbit supplies noncritical degree 4/16.
* Z(P)=Phi(P)=C2^4, the derived subgroup is C2^3, and P has exponent four.

Run the standard-library Python verifier from the repository root:

    python3 computations/python/verify_degree16_quotient.py

An optional positional argument selects another certificate file. Malformed
or rejected data produce a nonzero exit status. The default path is resolved
from the script location, so the command also works from another working
directory. No GAP installation, group catalogue or research-workspace files
are required. Python 3.9 or later is sufficient.

See the [data contract and verification argument](schema/degree16_quotient.md).

## Three degree-8 quotient charts and shared-source checks

The [degree-8 data](data/degree8_quotient_charts.json) give three literal order-32
actions, their order-2 normal axes, and maps from each action and one order-64
degree-8 cover onto the same order-16 quotient. The quotient's regular
degree-16 representation is auxiliary; the replacement's physical degree
remains eight.

The [local GAP package](../computations/gap/README.md) checks all four charts,
including 97 correlated full-preimage controls, and the shared-C3 moment
fixture. Its default mode uses literal permutations without catalogue
identification. The degree-8 exporter is an optional untrusted candidate
producer; the committed data suffice to run the checks.

    python3 computations/gap/run_local_checks.py

See [the finite coverage contract](../docs/blueprint/FINITE_CERTIFICATES.md)
for the distinction between these local charts, the complete small-width menu
and exhaustive action/normal coverage.

## Role in the proof

The degree-16 chart is one of the four exceptional local entries in the complete
small-width theorem. For any exterior group J and subgroup H<=U x J containing
N x {1}, the map pi x id_J satisfies

    H = (pi x id_J)^(-1)((pi x id_J)(H)).

Indeed its kernel is N x {1}; every preimage of an element of the image differs
from a member of H by a member of that kernel. This preserves correlations with
the exterior group. Applying the generic simultaneous-transport and weighted
mixture theorems then requires their separate hypotheses and proofs.

The local chart verifier establishes the literal chart. It does not check the
catalogue identifiers, uniqueness of this normal axis, exhaustiveness of the
finite menu, the full transport theorem's weights, or the subgroup asymptotic.
The separate complete-menu verifier supplies the finite coverage check.
These computations do not constitute Lean verification.
