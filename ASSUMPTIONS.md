# Mathematical inputs and computational evidence

Read with the [mathematical statements](SPEC.md) and
[external input register](provenance/LITERATURE.md).

## Mathematical assumptions

The argument uses ordinary finite group theory, linear algebra and analysis,
together with the external theorems identified in the input register. The
capacity, fusion, mixed-family, transport and exhaustion statements of this
project are mathematical components of the argument, not additional external
axioms.

The primitive results used in the c=1 application include classification-based
inputs. The argument is not claimed to be CFSG-free. Binary action coverage,
nonbinary transitive classification and primitive classification have distinct
scopes.

Every application of an external bound retains its actual group action,
faithful degree, normality and coefficient-field hypotheses. An abstract
quotient need not inherit the faithful permutation degree of its source.
The source list distinguishes journal articles from public preprints and
states the precise attribution where a result is quoted through another paper.

## Finite witnesses and coverage

Three mathematical assertions have different meanings:

1. Local soundness: acceptance of the serialized permutations, maps and
   inequalities implies the stated property of that finite witness.
2. Coverage: every action and normal subgroup in the theorem's quantified
   domain is represented, with valid transport under permutation conjugacy.
3. Evaluation: a specified checker accepts the particular supplied data.

GAP/Python checks provide computational evidence about the supplied witnesses.
A PASS message, file digest or collection of correct examples does not establish
coverage or a formal theorem. An action catalogue's completeness also does not
by itself establish the completeness of a normal-subgroup enumeration.

The complete binary-menu checker supplies explicit evidence for both coverage
claims: all transitive index-two kernels from Sylow wreath roots and all
central-involution extensions from the trivial normal. The mathematical
closure arguments are in the [binary schema](certificates/schema/binary_menu.md).
Its verifier uses literal permutations and GAP algorithms, without catalogue
queries or `NormalSubgroups`. Catalogue completeness remains a separate input
for the nonbinary and primitive ranges listed in the literature register.

The other finite packages specify their own completeness evidence in the
[certificate inventory](certificates/README.md). Nonbinary normal menus use
class-normal joins; pair-top and four-block menus use intersections of actual
irreducible kernels. The primitive/rank checker and the affine-nine constructor's small local
groups instead use GAP's normal-subgroup algorithm for those lists. Constructive block
coverage and catalogue-based coverage are kept distinct. Exact cyclotomic
characters, conjugacy, presentations and normalizers remain GAP computations.
The original zero-ternary frame bounds now have structural Lean proofs.
The eligible eight-point actions use actual Sylow-normalizer point witnesses,
valid for every local epimorphism and twist. The four-by-four branch uses a
common envelope for the whole original quotient socle and the actual Sylow
centralizer dichotomy; it requires no four-by-four top or module-lattice
census. Primitive frame coverage retains the explicit published classification
input and checked point-conjugacy bindings. These frame results and the complete
degree-four residual constructor are components of the constructed degree-two
joint catalogue, complete sixteen-pair source coverage and final composition.
Their recursive source/object release audit has passed. The complete six-pair
B6 source is now constructed uniformly from actual top geometry. The
required eight-pair source endpoint is now proved uniformly from the existing
published degree-eight action classification; it does not require the
alternative 527-entry ambient source table. The historical computational menus
are evidence for their own supplied witnesses, not extra hypotheses of these
structural frame theorems.

For the four exceptional charts, the data retain maps alpha:U->Q and beta:P->Q
onto the same specified quotient, with exact kernels and unchanged physical
degree. The degree-16 image is the actual proper subgroup
P<C4 x D8^3; replacing it by the full direct product changes the joint
relations. Simultaneous full-preimage transport keeps all correlated outside
coordinates. Its general weighted estimate is distinct from a finite inverse
check.

A supplied set of normalizer generators proves only a lower bound for the
normalizer order unless completeness is separately established. Exact action
weights use the normalizer in the original symmetric group, not an abstract
automorphism-group order.

The binary menu retains full symmetric normalizers for every action node;
the checker computes their equality with GAP's normalizer algorithm. The
separately pinned base alphabet fixes the actual carrier colours, rather than
allowing substitution of any actions satisfying the same numerical budgets.

The [certificate documentation](certificates/README.md) and
[local computation documentation](computations/README.md) specify the scope
of each supplied check. These computations do not constitute Lean verification.

## Formal theorem boundary

The formal targets are the three quantified statements T1, T2 and T3 in
[SPEC.md](SPEC.md). A formal result must state which of the following scopes
it establishes:

* **Conditional assembly:** the final implication is proved with some project
  components still supplied as explicit hypotheses. This proves the
  implication, not those components or the complete research argument.
* **Verification relative to published inputs:** all project-specific
  structural, counting, weighting, transport, analytic and finite-certificate
  arguments are checked proofs. Any remaining published mathematical result
  is an explicit named hypothesis, with its full proposition and source
  locator. This is the first intended substantive formal milestone.
* **Closed theorem:** all mathematical inputs, including the published ones,
  have checked proofs. Only the declared standard logical foundations remain.

The literature register supplies candidate external results, not a blanket
assumption that its contents are formalized. Every retained published input
must be individually specified and its exact scope audited. Its hypothesis
must remain visible in the final theorem type until it is discharged; a
global axiom declaration must not conceal it.

No project capacity, fusion, mixture, exhaustion or quantitative summation
claim may enter the published-input list. Acceptance or completeness of the
supplied action, normal-subgroup, character or module data must also be proved.
A published structural classification may remain an explicit literature
input in the relative milestone; correspondence with, and coverage by, the
concrete certificate list remain project proof obligations.

Finite verification has three separate obligations: soundness of the checker,
coverage of its quantified domain, and checked acceptance of the supplied
data. GAP/Python output and file hashes discharge none of these in Lean.
The intended certified computation uses kernel-checked reductions or proof
objects, with no additional unreported computation axioms. The release review
must inspect both the full theorem types and their transitive axiom
dependencies; an unproved theorem passed as an argument can be absent from an
axiom report while remaining a mathematical assumption.

The legacy `PublishedDegreeTwoFourPairClassification` and
`RDTMarkedC4ReductionInput` are certificate-valued interfaces, not accepted
literature assumptions. Their active constructions are now checked:
[`FourPairCanonicalClassification.classification`](formal/SymmetricSubgroupAsymptotics/FourPairCanonicalClassification.lean)
builds the four-pair certificates from the published action classification,
and
[`ActualGlobalMarkedMoment.marked_bound`](formal/SymmetricSubgroupAsymptotics/MarkedC4ActualGlobalMarkedMoment.lean)
constructs the full marked moment from its fifteen explicit ordinary
published inputs. Neither certificate-valued interface remains a project
hypothesis of the current published-input T1 facade.

The earlier
[conditional adapter](formal/SymmetricSubgroupAsymptotics/MarkedC4PublishedDegreeTwoT1.lean)
accepts degree-two source data. The current
[final facade](formal/SymmetricSubgroupAsymptotics/MarkedC4PublishedGeometricTargets.lean)
constructs those data internally. Its eight-pair endpoint is supplied by
[`PairedEightActualRepresentativeSource`](formal/SymmetricSubgroupAsymptotics/PairedEightActualRepresentativeSource.lean),
using only the existing published degree-eight classification, Zmud and
character-literature inputs. It retains the literal pair action, every
original normal denominator and all top-map fibres. The 527-entry source
table is an alternative construction of this endpoint, not an additional
T1 obligation. The full six-pair source is also proved by
`SixPairActualCompleteRepresentativeSource.representativeSource`: primitive
tops use the existing source, and the actual three-pair/two-triple top
geometries have nonbinary quotient socle capacity one. The universal natural
module has capacity two; binary original quotients have order at most 32.
All original axes and hot fibres are summed inside the unchanged width-12
menu. Actual sixteen-pair source coverage is now proved by
`DegreeSixteenCompleteGeometricSource.residualSource`, using actual minimal
blocks and complete original quartet sources. All 283 joint-catalogue entries
and the degree-two composition are also checked. The input reductions below
are now constructed; the separate recursive release audit passed on
20 October 2026.

Standard classical logical foundations are permitted. Unproved project
lemmas, proof placeholders and hidden certificate-acceptance assumptions are
excluded from either substantive verification milestone. The c=1 application,
shared-C3 moment and inverse-complement compatibility remain required checked
applications of the reusable results. Source verification, computational
replay, manuscript review and formal proof are reported separately.

The degree-sixteen locator is not an admissible literature assumption as
currently typed. Its four listed classes omit imprimitive, pair-free tops
with nonzero ternary local action, such as `A4 ≀ C4`. The existing 64 finite
row proofs remain valid within their hypotheses; they do not prove this
coverage proposition. The active replacement retains the actual minimal
block system. The pair, primitive and two-primitive-eight-block branches
now have complete checked width-32 sources, and the four-quartet constructor
is proved for both zero and nonzero odd local kernels. Their assembly
constructs `DegreeTwoSixteenPairResidualSource` from the bare published
degree-eight and primitive-degree-sixteen classifications, the published
socle and McIver--Neumann inputs, Zhmud and character literature. No
project-owned sixteen-point coverage proposition is assumed.

The final input audit exposed three older boundaries. The exceptional
Tracey `5/16` head bound is now proved by
`traceyBinaryExceptionalThree_of_raw` from the raw soluble formula and
Corollary 3.12 orbit data. The actual-wreath Clifford faithfulness conclusion
is now constructed by `CliffordRawRestriction.Input.toHomogeneousRestriction`
from the normal-restriction theorem. The latter is now proved over arbitrary
fields by `CliffordRawRestriction.proved`, so it is no longer an external
parameter. Both constructors have checked
sources and standard-only axiom audits. The corrected small-affine
representative receipt is now constructed for all 34 fixed rows by
`SmallAffineCanonicalRepresentatives.receipt`. It takes bare published
catalogue coverage and internally supplied proofs of `PSL₃(2)`/`PSL₃(3)`
simplicity and Burnside's `p^a q^b` theorem, with no representative-facts or
composition bound input.
Its structural alternatives permit central abelian factors; the former
invalid uniqueness condition has been removed. The degree-twenty-five
projective-to-composition deduction is now proved from the actual
`GL₂(5)` embedding, `PGL₂(5) ≅ S₅`, Burnside's theorem, and internal
subgroup and chief-order arguments. It also constructs the actual scalar
`C₄` datum. The complete finite affine package is built by
`PublishedPrimitiveAffineFiniteLiterature.ofCanonicalClassifications`;
neither a representative receipt nor an affine-capacity bound is assumed
at the updated geometric target facade.

The quantitative `PublishedPrimitiveSocleDichotomyInput` is now constructed
by `PrimitiveSocleRawStructure.PublishedONanScottStructure.toSocleDichotomy`.
Its inputs are ordinary O'Nan–Scott full-socle/degree structure and the two
published simple-index inequalities of Ballester-Bolinches,
Esteban-Romero and Jiménez-Seral. Least-index selection, the lower bound
five, the faithful outer-wreath action, all numerical degree/logarithm
deductions, and the exact original one-factor quotient are proved
internally. The rounded all-subgroup generator bound is likewise derived
from the retained McIver–Neumann theorem.

Four previously retained inputs are now checked theorems: Burnside's
two-prime solvability theorem; arbitrary-field Clifford restriction;
the weak binary normal-subgroup estimate (from the stronger proved
Palcoux–Spiga subgroup-interval bound); and simplicity of `PSL₃(F)` for
every field. The last proof uses elementary matrices and Iwasawa's
criterion, with Apache-licensed mathlib backports and no ATLAS source.
Their adapters are inserted directly in the final target facade.
No corresponding argument is required from a caller of T1 or AllTargets.
Exact upstream revisions and licensing are in
[the external proof notice](formal/SymmetricSubgroupAsymptotics/External/NOTICE).

The exceptional `PGL₂(F₅) ≃ S₅` isomorphism and the complete degree-five
affine classification are now also proved internally. The former uses the
actual six-point projective action and an order-120 subgroup recognition
lemma in `S₆`; the latter constructs literal affine coordinates and retains
the original action conjugacy in the `F₂₀` branch. No classification,
finite-table, or ATLAS premise is added. The two older induced-module
half/logarithmic inputs are derived from the retained refined Tracey input,
and the faithful-simple generator input is derived from the retained
finite-simple two-generation input. These three are dependency reductions,
not formalizations of the stronger retained results.

The final T1 and AllTargets exports compile with these raw inputs. A fresh
audit of both exports, `T2_of_T1`, `T3_of_T1`, `allTargets_iff_T1`, and
`definitionChecks` reports exactly `propext`, `Classical.choice`, and
`Quot.sound`. The complete
41-parameter mathematical boundary, with formulations and source locators,
is listed after the bounds and folder structure in [formal/README.md](formal/README.md).
No project capacity, source, marked-moment, affine-consumer or quantitative
socle-profile premise remains in those signatures. Ordinary published
counting theorems and explicitly described finite structural catalogue
correspondences remain assumptions. On 20 October 2026 the recursive
source/object audit passed for all 5,905 project modules in the public
import closure. Every source in that closure is tracked in main and matches
the audited bytes. Optional modules outside the closure and the source
contents of pinned external package objects are outside that audit's scope.
This establishes the verification-relative-to-published-inputs milestone
defined above; it does not claim formal proofs of the retained literature
inputs. Detailed receipts and audit records remain outside the publication
repository.
