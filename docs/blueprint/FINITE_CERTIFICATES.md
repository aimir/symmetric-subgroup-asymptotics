# Finite certificates and their mathematical scope

This document distinguishes the supplied local chart checks from the
exhaustive coverage certificate for the small-width theorem. Local
map verification alone proves neither exhaustive coverage nor an asymptotic
counting bound.

## 1. Independent mathematical claims

The complete small-width interface quantifies over every actual transitive
binary action U of degree 2, 4, 8 or 16 and every literal normal N. Its
components have different conclusions:

| Component | Mathematical conclusion |
|---|---|
| Local predicate soundness | A central-prefix cut, strict faithful quotient cover or whole-quotient binary character certificate gives its stated complete-source bound. |
| Action and normal coverage | Every entry outside the specified base alphabet admits a strict certificate or a replacement chart. |
| Literal chart correctness | Both maps are onto the same quotient, have their stated exact kernels and use the same physical degree with full target projections. |
| Simultaneous transport | The entire joint quotient relation and actual original subgroup are recovered, including proper subdirect cores. |
| Weighted mixture bound | Decorations and all action/occurrence weights fit the original profile reserves, including small noncritical support. |
| c=1 compatibility | Surviving characters, shared-C3 moments and inverse-complement weights retain their exact same-source meanings. |

The coverage interface is relative to a specified base alphabet of actual
permutation actions; degree or abstract group isomorphism does not identify
an action. The critical actions and regular C4 are base actions in the
mixed-family application. The binary degree-2/4 boundary is C2,C4,V4,D8.
Regular binary actions of width at least eight admit a generic all-normal
central-involution argument, which is distinct from enumerating examples.

## 2. Local chart and common-source checks

The entry point is
[computations/gap/run_local_checks.py](../../computations/gap/run_local_checks.py).
It resolves all input paths relative to this repository.
Its JSON inputs are
[degree16_quotient.json](../../certificates/data/degree16_quotient.json) and
[degree8_quotient_charts.json](../../certificates/data/degree8_quotient_charts.json).
The degree-16 chart also has an independent standard-library Python verifier.

The GAP checker proves computationally that each supplied map is a homomorphism
and onto, and that its actual kernel equals the literal subgroup in the data.
It computes, rather than assumes, source/image orders, transitivity and the
required projection data. It also checks uniqueness of the relevant normal
order 2/order 4 axes using GAP's normal-subgroup algorithm. That last check is a
local claim for the supplied groups, not complete small-width coverage.

The three degree 8 charts have a physical degree8 replacement. Their common
quotients are encoded as regular degree16 permutation groups only to make the
maps literal. Those auxiliary16 points must never be added to the physical
word. All three sources use the same literal degree 8 carrier, with separately
retained source kernels and map images.

The degree 16 image is literally the order 256 subgroup P of
C4[4] x D8[4]^3. The code keeps P, not the full order 2048 product. It verifies one
correlated P x C2 exterior and the whole full-preimage inverse. The degree8
controls similarly check all 32 automorphisms of each quotient, giving 96
correlated fibres. These finite inverse checks illustrate the general theorem;
they do not establish its weighted version or all possible exterior groups.

The separate
[shared-source GAP fixture](../../computations/gap/verify_shared_source_moment.g)
checks A4 -> C3 over the two actual sources C3 and C3^2 by subgroup-first
enumeration. Its records are [[2,4,0,4],[8,64,48,80]], with columns defined in the
GAP README. The full joint quotient image is not required, and the same source
is used in both map positions. This fixture asserts no catalogue coverage.

The runner supports either a `gap` executable or `sage --gap`. Commands,
input conventions and expected local verdicts are documented in
[the GAP README](../../computations/gap/README.md).

The separate Lean module
[BinaryExceptionalCarriers](../../formal/SymmetricSubgroupAsymptotics/BinaryExceptionalCarriers.lean)
installs all four literal charts. Finite Cayley tables, generator words and
graph-kernel checks prove the actual homomorphisms, their exact images and
both original kernels. The generic transport proof then recovers the full
original subgroup with any exterior group, including nonabelian exteriors.
Actual block restriction maps identify the physical carrier projections and
their positive noncritical support. The
[exporter](../../computations/python/export_lean_carriers.py) generates
untrusted Lean witnesses from the committed data; neither GAP verdicts nor
catalogue orders are proof premises. This establishes these four charts,
not the complete coverage contract below.

## 3. Complete coverage contract

A complete finite certificate for the boundary quantifies over every actual
transitive 2-group U<=S_w, w in {2,4,8,16}, and every literal normal subgroup
N of U. The action and normal are transported together under permutation
conjugacy. Every entry outside the specified base alphabet satisfies at
least one of the following alternatives:

* An actual invariant pair frame and central cut with
  v_B+2dim(C)+4dim((A/C)^B)<w, retaining the same section
  A=K/(K intersect N).
* A faithful permutation representation of the actual U/N on fewer than w
  points, with its literal kernel verified.
* An exact central binary rank z satisfying 38^(8z)<2^w·25^(8z), together
  with the whole-quotient character theorem in its stated source scope.
* A literal same-degree replacement chart with the actual source axis,
  common quotient and positive noncritical target fraction.

Witness soundness, exhaustiveness of the normal-subgroup list and coverage
of all permutation actions are separate assertions. Equal abstract quotients
do not identify different literal normals. Cached quotient representations
have to carry their actual transported maps.

The [complete binary menu](../../certificates/data/binary_menu.jsonl.gz) retains
these witnesses for each nonbase normal, together with two coverage graphs.
Every transitive index-two child of each action is checked, starting from an
explicit Sylow wreath group. Every central-involution extension of each
normal is checked, starting from the identity. The
[schema and mathematical coverage arguments](../../certificates/schema/binary_menu.md)
explain why closure gives the two universal quantifiers. Original symmetric
normalizers are recomputed exactly for every action node, and the base colours
are bound to the [fixed literal alphabet](../../certificates/data/base_alphabet.json).

Run `python3 computations/gap/finite_menu.py verify`; the
[reproduction documentation](../../computations/gap/FINITE_MENU.md) describes
candidate export and the computational trust boundary. Replay does not use
transitive catalogue queries or `NormalSubgroups`. This binary certificate
has no coverage claim for the separate nonbinary or primitive finite inputs.

In Lean, `BinaryCoverage` proves the two generic registry implications:
index-prime action closure and central-prime normal closure give exhaustive
coverage. The full menu's literal closure edges and accepted leaf outcomes
have not yet been installed in those theorems. Computational replay of the
complete data and kernel checking of the four charts therefore have distinct
verification scopes.

## 4. Carrier finite inputs

The base alphabet's mixed-family argument has a separate
[carrier certificate](../../certificates/schema/carrier_transitions.md).
Its eight master actions retain all 14,008 literal normal kernels and their
six-parameter profiles. Central-involution closure supplies normal coverage.
Seven literal generator-image maps route the original degree-eight colours
through the masters with their original normalizer weights intact.

The companion rational checker verifies all old and new domination columns,
both marking parameters and both quadratic cone certificates. This supplies
the exact finite transition reserve consumed by the mixed-family estimate.
The source-independent rank-transition, radical transport and attachment
lemmas remain mathematical premises of that estimate.

## 5. Other finite theorem inputs

The [certificate inventory](../../certificates/README.md) supplies separate
contracts for the nonbinary degree-16 partition, overlapping primitive and
relative-rank ranges, count-twelve/count-sixteen pair tops, constructive
four- and six-block actions, the affine-nine Goursat/swap construction,
and the carrier Bockstein socket. The critical quadratic constant has an
independent exact binary-matrix enumeration.

Action coverage in a pinned primitive/transitive catalogue is an external
classification premise. The checkers verify the actual catalogue slice where
required. Constructive packages instead retain complete adjoining, generator
lift or graph/swap evidence. Normal coverage is proved by central-involution
closure, class-normal joins or irreducible-kernel intersections as specified
by each schema. Primitive/rank lists and small local normal lists in the
affine-nine construction explicitly use GAP's normal-subgroup algorithm. These are distinct computational boundaries.

The binary module package rebuilds each full invariant lattice and tests
simple sections and same-generator Hom spaces. The original width and
all-normal character entries are checked separately. Section ranks alone do
not supply the general retained-annihilator capacity theorem, nor do finite
covers supply its source-counting and weighted aggregation arguments.

## 6. Scope of finite evidence

A normalizing generating set proves containment in the action normalizer,
not its exact order. Critical coefficients using an exact a(U) need that
exactness, rather than an abstract automorphism count.

A numerical cost for a module cut does not imply its source-independent
lifting bound: the actual quotient and retained transgression annihilator
enter that bound. Likewise local reversibility does not bound the decoration
fibre. The transport estimate uses the mixed-family profile reserves after
handling the small-support strip.

The supplied shared-source and inverse-complement controls test finite
instances of the incidence identities. They do not close arbitrary c=1
families. None of these local checks alone proves the complete weighted
small-width theorem, the unbounded-width theorem or the subgroup asymptotic.
