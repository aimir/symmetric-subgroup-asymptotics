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
queries or `NormalSubgroups`. The historical catalogue packages have separate completeness contracts;
none of those correspondences is a premise of the current final T1 export.

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
census. The current primitive frame consumer uses actual translation kernels;
stronger optional classifiers retain their separate coverage contracts. These frame results and the complete
degree-four residual constructor are components of the constructed degree-two
joint catalogue, complete sixteen-pair source coverage and final composition.
Their recursive source/object release audit has passed. The complete six-pair
B6 source is now constructed uniformly from actual top geometry. The
required eight-pair source endpoint is now proved uniformly from the existing
proved degree-eight action classification; it does not require the
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
[final facade](formal/SymmetricSubgroupAsymptotics/MarkedC4PublishedTenTargets.lean)
constructs those data internally. Its eight-pair endpoint is supplied by
[`PairedEightActualRepresentativeSource`](formal/SymmetricSubgroupAsymptotics/PairedEightActualRepresentativeSource.lean),
using the internally proved degree-eight classification, Zmud and
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
the actual source in `DegreeTwoSourceWithoutTwelveOrSixteenCatalogue.lean`,
using actual minimal blocks and complete original quartet sources. All 283 joint-catalogue entries
and the degree-two composition are also checked. The input reductions below
are now constructed; the separate recursive release audit passed on
20 October 2026.

Standard classical logical foundations are permitted. Unproved project
lemmas, proof placeholders and hidden certificate-acceptance assumptions are
excluded from either substantive verification milestone. The c=1 application,
shared-C3 moment and inverse-complement compatibility remain required checked
applications of the reusable results. Source verification, computational
replay, manuscript review and formal proof are reported separately.

The old four-class sixteen-point locator is insufficient: it omits
imprimitive pair-free tops with nonzero ternary local action, such as
`A4 ≀ C4`. Its local row proofs do not imply coverage. The current source
instead retains the actual minimal block system, and its primitive,
pair, four-quartet and two-primitive-eight-block branches are all proved.
The primitive branch now uses the original elementary translation kernel;
no primitive-sixteen correspondence is needed. The same actual-source
route also removes the transitive-twelve correspondence.

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
The ordinary O'Nan–Scott full-socle/degree structure is now proved internally;
the remaining inputs are the two published simple-index inequalities of Ballester-Bolinches,
Esteban-Romero and Jiménez-Seral. Least-index selection, the lower bound
five, the faithful outer-wreath action, all numerical degree/logarithm
deductions, and the exact original one-factor quotient are proved
internally. The rounded all-subgroup generator bound is likewise derived
from the retained McIver–Neumann theorem.

The optional concrete CFSG reduction proves both simple-index inequalities
for alternating groups, every original type-A model, and Suzuki groups.
The type-A outer bound uses a proved projective-frame count, with no
semilinear-classification premise. Other literal model cases remain explicit
in `publishedSimpleIndexBounds_of_cfsg_and_remaining_non_typeA_suzuki_models`;
the global published simple-index input is therefore still retained by T1. The optional reduction also proves
`ell^2 < |G|` for every original type-C model, using actual symmetric
shears and an injective augmented cell. Its outer-automorphism inequality
is still open, so type C is not yet removed from this global input.
The original elementary matrix realization is also proved to be the full
natural symplectic group by a Gaussian base case and hyperbolic-pair
stabilizer induction; this identification is not an extra assumption.

The same optional reduction proves two-generation for every original type-C
model, using explicit matrix pairs and the proved Serre-projective
realization. Together with type A, Suzuki and the previously proved finite
cases, these are removed by
`finiteSimpleTwoGeneratorBound_of_cfsg_and_remaining_non_typeA_suzuki_C_models`.
The other model cases remain explicit, so the global published
two-generation input is still retained by T1. The corresponding
original type-D family is now also proved in full, all ranks at least
four and all prime-power fields. Its exact residual adapter is
`finiteSimpleTwoGeneratorBound_of_cfsg_and_remaining_non_typeA_suzuki_C_D_models`;
other model families still remain.

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
half/logarithmic inputs are derived from the internally proved refined
induced-module theorem. The faithful-simple generator input is derived from
the retained finite-simple two-generation input; that latter dependency
reduction does not formalize the stronger two-generation theorem.

The degree-six and degree-nine primitive inputs are now derived from the
retained 336-row composition catalogue. The degree-six proof constructs
maximal-overgroup coset actions and uses the catalogue at degree twelve;
it does not insert an order-60 recognition assumption. The binary formula
is derived from the proved refined theorem, and the soluble permutation
formula from its soluble-orbit induced-module input. Actual stabilizer
induction, an explicit uniform integer cap, and a proved odd Hall subgroup
existence theorem supply the transport. The last theorem uses mathlib's
Schur–Zassenhaus theorem and introduces no new literature premise.
The duplicate standalone Kovács–Praeger parameter is supplied by the
proved full abelianization theorem. These five earlier parameter removals leave the broader
published catalogue, refined Tracey and soluble-orbit inputs explicit.

The soluble subdirect socle-height statement is now proved unconditionally.
The proof identifies the exact intersection of factor-socle inverse images
using semisimple integral conjugation modules, then passes to the actual
socle quotients. Both degree-six block classifications are also proved
unconditionally through explicit faithful wreath charts: the three-pair
and two-triple interfaces no longer require published catalogue inputs.
Their original source predicates and retained action data are unchanged.
The standalone Dixon order bound is derived from the retained primitive
catalogue and the proved O'Nan–Scott structure. Its large affine step now
uses elementary linear-map counting, followed by actual block and orbit
induction. The soluble irreducible linear cube premise is also removed:
the degree-81 complement bound follows from the retained primitive
composition theorem, the exact GL₄(F₃) order and a checked prime-factor
budget. Neither consumer uses the general Halasi–Maróti theorem.

The full order bound for abelian p-quotients is now proved from faithful
p-group actions and actual Sylow restriction. It includes higher prime-power
cyclic factors, so the binary character-literature field is filled internally;
the mixed-prime bound is proved using an actual nilpotent supplement and
disjoint coprime supports, rather than multiplying prime bounds on the same
degree. The `PreE7CharacterPublishedInputs` bundle now has only the general permutation class-number
field. The nilpotent class bound is proved from prime-group fourth-power
estimates and actual disjoint coprime supports. The exact faithful-character tuple theorem and bounded-factor
epimorphism theorem are also proved internally; neither is a T1 assumption.
The degree-eight affine-complement locator is proved from complete checked
coverage of the15 actual GL(3,2) subgroup classes. Its remaining catalogue
parameter requests only the31 fixed complement rows in degrees16 and27.

The derived-normal quarter bound is proved by original-degree induction
through the actual central-pair kernel and faithful top image. Its kernel
quarter estimate for a nonelementary top is proved uniformly; an elementary
top kills the derived image. This does not assume binary excess classification.
The raw O'Nan–Scott theorem is proved from actual minimal normals, faithful
primitive point stabilizers, the proved Scott subdirect theorem, and the
exact automorphism/inner-kernel structure of simple powers. It retains the
full socle and the original quotient embedding. Neither theorem remains a
parameter of the final exports.

The ordinary dependent-word normal-generation theorem is derived from the
now-proved exact binary excess classification and the proved universal
proper-normal ceiling. Its literal dependent factors, maximal full tail,
and three numerical prices are preserved. The separate h55 parameter is
removed; the exact h53 classification is also proved internally.

The separate soluble nilpotent-generation input is also removed. The
proved bounded-chief-section theorem gives a nilpotent core and at most
`L*(B!+1)*floor(sqrt M)` ordinary supplement generators. Actual bounded
orbit images give `L=B=C!`, and the proved abelian-section estimate gives
`M=2b`. The global marked-moment proof retains the original orbit cutoff C;
only its fixed tuple-control constant is enlarged. The unrestricted sharp
`4L*sqrt M` assertion is not claimed as proved and is not needed by T1.

The degree-eight binary excess-two implication is proved by complete checked
coverage of all 26 binary actions. The other 25 actions have at most three
ambient normal generators for every normal subgroup, certified by short
conjugate-product words and complete normal registries. The surviving E8
model has center equal to its derived subgroup, of order two; every
nonabelian normal quotient therefore has trivial denominator. No action
classification hypothesis is added.

The large-orbit ordinary generator estimate is derived from the retained
primitive normal-generator and primitive composition-length inputs, together
with the internally proved refined induced-module theorem. Its induction retains all original orbit correlations and lifts
ordinary generators only across actual abelian chief kernels. The stronger
checked bound is 128 times the sum of n_i/sqrt(log₂ n_i) over nontrivial
orbits; a rate-only integer power-of-two cutoff gives the former h62 field.
The final marked moment also avoids h86: the constructed actual soluble
cover has `2^(O(b log⁴(b+2)))` labels, and the same original relative-tuple
encoding pays that menu once. This branch now needs no labelled-transitive
count premise. The independent nonsoluble pre-E7 action menu still uses
the retained transitive-count theorem. This does not prove Pyber's sharper
exponential class bound.

The refined induced-module theorem is now proved in
`TraceyRefinedInducedModuleProof.lean`. It uses actual Sylow/Mackey indices,
finite chain widths, a proved binomial square-root estimate, Nakayama and
coprime semisimplicity; one least uniform integer satisfies all five fields.
The soluble-orbit input is also unnecessary for T1. Its exact permutation
consumer is proved by two capacities on the same original module, and its
degree-four consumer by the actual normal ternary core and cyclic quotient.
This replaces those consumers; it does not prove the stronger arbitrary-local
per-orbit statement.

The final actual-source route requires no finite action-catalogue
correspondence. Primitive chief weights and the 3/10 weight bound use
actual linear and full-socle structure, the retained composition-length
theorem and simple-index inequalities. The strict-head bound is used away
from degrees 10 and 12; the complete physical C3 source pays those two
actual semisimple sectors separately. Actual degree-eighteen heads and
semisimple compression give the remaining consumers. This does not assert
the stronger unused global strict-head theorem or the 336-row, 253-row,
31-carrier and 116-row correspondences.

The actual affine consumer assembly retains original block systems,
translation kernels and normal axes. At degree 16 it uses the proved
`GL₄(F₂) ≃ A₈` geometry; degree 27 uses proved linear structure. Complete
twelve-pair and sixteen-pair sources therefore require neither the
301-action transitive-twelve correspondence nor primitive-sixteen coverage.

The final T1 and AllTargets exports have ten explicit published inputs,
with their mathematical formulations and source locators listed after the
bounds and folder structure in [formal/README.md](formal/README.md).
The exact binary normal-F theorem is now proved without hypotheses as
[`publishedTheorem57Binary_proved`](formal/SymmetricSubgroupAsymptotics/BinaryNormalFTheorem57Proof.lean).
It retains the ambient commutator `[F,Q]`, actual centralizer, original
nonabelian quotient and every excess/rank alternative. Its proper-normal
constructions keep the same original denominator and actual affine cocycle;
no split-extension or capacity statement is assumed.
The remaining ten inputs are the published general counting,
composition, generation and simple-group inequalities listed there. No project capacity,
source, marked-moment, affine-consumer or quantitative socle-profile premise
occurs in those signatures.

The axiom audit reports only `propext`, `Classical.choice` and `Quot.sound`.
Recursive source/object verification checks the current local import
closure against successful receipts and pinned toolchain fingerprints.
Optional modules outside that closure and the source correspondence of
installed external package objects are outside its scope. Detailed receipts,
audits and research status records stay outside the publication repository.
This is verification relative to the listed published inputs; it does not
claim formal proofs of those remaining inputs.

The optional CFSG route also proves the exact order of every finite natural symplectic group internally (`CFSGSymplecticCardinality.elementary_card` and `symplectic_card`, in the stabilizer-coordinates namespace). This supports the ongoing outer-automorphism calculation; it does not discharge another entire public T1 input.

Characteristic-two type-B generation is also proved internally on the pinned original model, with its actual matrix image identified with the elementary C group (`CFSGOrthogonalBGenerationCharTwoReduction`). Only binary-characteristic B tags are removed from this optional generation residual; the public T1 boundary still retains ten independent published inputs.

The shared exceptional route now derives the actual finite E6/E7/E8 root systems and rational Geck representations internally, including the coordinate base, irreducibility and exact Cartan binding. These results discharge root-system construction prerequisites only. The integral/group-image steps and the exceptional quantitative model bounds remain open, and the public ten-input boundary is unchanged.

The complete original type-C simple-index packet is now proved (`CFSGSymplecticSimpleIndexReduction`). The actual outer group has order at most twice the field-automorphism count in odd characteristic and three times in characteristic two. The latter charges the original natural-root family stabilizer index before counting; no projective-automorphism lift is assumed. Together with the proved squared-index bound, this removes all C tags from the optional simple-index residual. The whole published simple-index input is still retained for the other open model families.

The full original B two-generation packet is also proved (`CFSGOrthogonalBGenerationReduction`), including the odd-characteristic three-element field. The quadratic-root parameter extraction and cleaned signed orbit recover every original defining root, and the prior characteristic-two route remains unchanged. All B tags are now removed from this optional generation residual. Exceptional/twisted Lie families and six sporadic generation cases remain; this does not remove the entire public simple-generation input.

The characteristic-two B simple-index branch is now also proved (`CFSGOrthogonalBCharTwoSimpleIndexReduction`). Its original source is identified with the actual projective C matrix group by a faithful-image argument and centre-quotient transport. The complete C estimates therefore apply with simplicity transferred from the original B source. Odd-characteristic B and the other open families remain explicit in the simple-index callback.

The generic primitive-input foundations (`CFSGCompositionLengthCardinality.lean`, `CFSGSubnormalSimpleProduct.lean`, `CFSGSimpleProductCompositionLength.lean`) now prove that every actual composition series has length at most log₂ of the original group order; every subnormal subgroup of a finite product of nonabelian simple groups is a literal coordinate product; and every composition series of that product has length at most its number of original factors. These are proved without CFSG or a Jordan–Hölder input. They do not discharge the sharper primitive composition-length or normal-generation bounds.
