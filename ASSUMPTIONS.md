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
degree-four residual constructor are distinct from the still-unfinished
degree-two joint catalogue and final composition. The complete six-pair
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

That [facade](formal/SymmetricSubgroupAsymptotics/MarkedC4PublishedDegreeTwoT1.lean)
still takes the project-owned degree-two source. Its eight-pair endpoint is
now supplied by
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
menu. The remaining joint-catalogue entry and final
coverage and final degree-two composition must still be completed before
claiming T1 with only published assumptions.

Standard classical logical foundations are permitted. Unproved project
lemmas, proof placeholders and hidden certificate-acceptance assumptions are
excluded from either substantive verification milestone. The c=1 application,
shared-C3 moment and inverse-complement compatibility remain required checked
applications of the reusable results. Source verification, computational
replay, manuscript review and formal proof are reported separately.
