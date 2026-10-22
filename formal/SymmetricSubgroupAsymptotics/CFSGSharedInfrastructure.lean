import SymmetricSubgroupAsymptotics.CFSGSimpleGenerationReduction
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexRemainingModels
import SymmetricSubgroupAsymptotics.CFSGEvenOrderRemainingModels
import SymmetricSubgroupAsymptotics.CFSGSolubleGenerationLifting
import SymmetricSubgroupAsymptotics.CFSGSolubleGenerationQuotients
import SymmetricSubgroupAsymptotics.CFSGSylowNormalizerGeneration
import SymmetricSubgroupAsymptotics.CFSGFiniteFamilyGeneration
import SymmetricSubgroupAsymptotics.CFSGJ4Generation
import SymmetricSubgroupAsymptotics.CFSGYSectionGeneration
import SymmetricSubgroupAsymptotics.CFSGPrimeTransitiveNormalBound
import SymmetricSubgroupAsymptotics.CFSGOrdinaryBoundedBinaryCount
import SymmetricSubgroupAsymptotics.CFSGSuzukiModelGeneration
import SymmetricSubgroupAsymptotics.CFSGTypeASuzukiModelGoodSylow
import SymmetricSubgroupAsymptotics.CFSGSuzukiModelCardinality
import SymmetricSubgroupAsymptotics.CFSGSuzukiEvenOrder
import SymmetricSubgroupAsymptotics.CFSGSerreRootDirection
import SymmetricSubgroupAsymptotics.CFSGSerreLocalNilpotence
import SymmetricSubgroupAsymptotics.CFSGSerreTwistGraphProjection
import SymmetricSubgroupAsymptotics.CFSGSuzukiSimpleIndexReduction
import SymmetricSubgroupAsymptotics.CFSGSerreOrdinaryTwistModels
import SymmetricSubgroupAsymptotics.CFSGSerreRepresentationDescent
import SymmetricSubgroupAsymptotics.CFSGSerreGeneratorRepresentation
import SymmetricSubgroupAsymptotics.CFSGPSLTwoSimpleIndexReduction
import SymmetricSubgroupAsymptotics.CFSGSerreEvenOrderRefinement
import SymmetricSubgroupAsymptotics.CFSGTypeATransvectionRecognition
import SymmetricSubgroupAsymptotics.CFSGTypeARootPermutation
import SymmetricSubgroupAsymptotics.CFSGTypeAOuterIndexNumerics
import SymmetricSubgroupAsymptotics.CFSGSymplecticImageCentralizer
import SymmetricSubgroupAsymptotics.CFSGSymplecticElementaryCenter
import SymmetricSubgroupAsymptotics.CFSGSymplecticProjectiveRealization
import SymmetricSubgroupAsymptotics.CFSGIncidenceOrientation
import SymmetricSubgroupAsymptotics.CFSGColorOrientationIndex
import SymmetricSubgroupAsymptotics.CFSGEquivariantAutomorphismFaithfulness
import SymmetricSubgroupAsymptotics.CFSGInnerActionFaithfulness
import SymmetricSubgroupAsymptotics.CFSGProjectiveLinearCardComparison
import SymmetricSubgroupAsymptotics.CFSGSymplecticEvenOrderRefinement
import SymmetricSubgroupAsymptotics.CFSGTypeASimpleIndexReduction
import SymmetricSubgroupAsymptotics.CFSGSubgroupFamilyFaithfulness
import SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryGenerationReduction
import SymmetricSubgroupAsymptotics.CFSGSymplecticGenerationReduction
import SymmetricSubgroupAsymptotics.CFSGSymplecticFormPreservation
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDEvenOrderRefinement
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDBinaryGenerationReduction
import SymmetricSubgroupAsymptotics.CFSGSymplecticMinimumIndexLower
import SymmetricSubgroupAsymptotics.CFSGSymplecticMinimumIndexUpper
import SymmetricSubgroupAsymptotics.CFSGSymplecticCenterCardinality
import SymmetricSubgroupAsymptotics.CFSGSymmetricMatrixCardinality
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBEvenOrderRefinement
import SymmetricSubgroupAsymptotics.CFSGSymplecticLeastIndexSquare
import SymmetricSubgroupAsymptotics.CFSGSymplecticHyperbolicPairOrbit
import SymmetricSubgroupAsymptotics.CFSGSymplecticFullGroup
import SymmetricSubgroupAsymptotics.CFSGSymplecticProjectiveNaturalRootLines
import SymmetricSubgroupAsymptotics.CFSGGTwoEvenOrderRefinement
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationReduction
import SymmetricSubgroupAsymptotics.CFSGSymplecticCardinality
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationCharTwoReduction

/-!
# Shared infrastructure for the reduction to concrete CFSG

The classification proposition is supplied by the frozen external statement.
It asserts existence of an isomorphism to an explicit model. Transport of
finiteness, simplicity, generation, least subgroup index and the actual outer
automorphism group is proved before quantitative model properties are used.

The alternating family's two-generation and simple-index bounds are proved
without classification; its exceptional degree-six automorphisms are handled
through their action on the two actual order-three conjugacy classes. Twenty
sporadic models have literal generating subsets of size at most two. The
remaining concrete cases are explicitly retained in the reduction theorems.

The literal type-A and Suzuki families now have checked two-generator
and good-Sylow witnesses. Suzuki's original matrix Bruhat decomposition
also supplies its exact order and normalizer intersection.
Suzuki's outer group has order at most the original field exponent,
and its actual least proper index satisfies the required numerical packet.
Shared integral
Serre divided-power and local-nilpotence lemmas support further Lie families;
every displayed root operator now has a checked invertible lift, including
after integral base change. These facts do not assert additive root
parameters, cross-root relations or the uniform finite-type nilpotence bound.
Diagram and field automorphisms now identify the literal graphs for the
ordinary twisted A, D, E6 and triality families. The exceptional long-short
isogenies remain separate.
The original rank-one type-A matrix model also satisfies both actual
least-index bounds, including field orders four and five by the same
argument. The entire type-A family now satisfies both required
simple-index bounds; other family cases remain explicit.
For higher-rank type A the squared-index inequality and the lower bound
`q^r <= ell` are proved on the actual matrix quotient. Transvections are
recognized by Sylow centres, and every automorphism permutes the original
full point-root and hyperplane-root groups. Actual PGL frame alignment
and the frame-stabilizer injection into field automorphisms give the
collineation count. Cancelling the actual inner group then proves
`|Out PSL_n(F)| <= 2*n*|RingAut(F)|` for `n >= 3`, discharging the
numerical adapter's outer premise.
Actual divided-power-stable kernels also support a descended action on
any surjective representation image. A simple source identifies its
projective quotient with the nontrivial projective image; this does not
assume or prove that the image is a named classical group. The six literal
Serre generator relations have a reusable quotient-map constructor.
The concrete symplectic matrices now satisfy those six relations over
the rationals, preserve the original integral lattice, and intertwine
every original root operator after base change. The action on this
actual image has scalar commutant. The full natural symplectic group
identification is proved by the later stabilizer induction.
Its action range is exactly that of the literal elementary matrix group.
When the original projective source is simple, this gives an actual
isomorphism to the elementary group's central quotient; no Lie-algebra
faithfulness or full classical-group generation is assumed.
In characteristic two every original root lift is an involution. Any
nontrivial quotient of an untwisted Serre model consequently has even
cardinality, without a matrix-group recognition hypothesis.
The symplectic realization also supplies a noncentral fourth root of
one in every characteristic, proving even cardinality for all original
simple type-C models. Their entire classifier branch is discharged
from the parity residual, including odd characteristic.
For field order two and every classifier-admissible rank, an explicit
Coxeter word and a disjoint order-three/root word generate the actual
elementary group. Transport through the same projective realization proves
two-generation for the original binary type-C models. Nonbinary type-C
models use a different explicit pair: full long-root extraction, actual
coordinate tori and signed Coxeter propagation recover every original
simple-root parameter. The three-element field has its own checked pair.
Thus every classifier-admissible type-C model is two-generated, and the
entire C branch is removed from the exact generation residual. The same
natural matrices identify with the full form-preserving symplectic group:
the rank-one Gaussian base and the actual hyperbolic-pair stabilizer
prove surjectivity in all ranks. This is a proved theorem, not an input.
The same first-pair stabilizer recurrence and an exact affine-fibre count
now prove the full finite order formula
`|Sp_(2*n)(K)| = q^(n*n) * product_(i=1..n) (q^(2*i)-1)`,
including ranks zero and one, with no published order premise.
The original untransposed type-D model now has the same complete
rational-to-integral image construction, using a shared square-zero
matrix realization. The two fork projections prove a scalar commutant
in every characteristic. Its actual elementary central quotient is
isomorphic to the original simple projective source. A noncentral
chain Weyl word of fourth power one proves even order for the entire
original type-D family, removing all D tags from the parity residual.
An actual generating pair also recovers all original simple roots for
every binary type-D rank at least four. The exact generation residual
omits the binary D tags. The subsequent nonbinary pair uses primitive
root-parameter extraction and signed star propagation; both endpoint
geometries recover the original short roots and Weyl word in the same
subgroup. Every original D model of rank at least four is therefore
two-generated, and all D tags are removed from the exact generation
residual. No full orthogonal-group recognition theorem is assumed.
For the original symplectic model, the actual short-root conjugacy
and a moved natural projective point prove `q <= ell` and
`ell*(q-1) <= q^(2*r)-1`. The natural centre has at most two elements
and is trivial in characteristic two. An injective block-cell chart
counts symmetric parameter pairs exactly. Every symmetric shear belongs
to the actual elementary group. An augmented cell with a two-coordinate
Borel factor proves `ell^2 < |G|` for every admissible original C model,
including characteristic two. Actual elementary words also move every
nonzero natural vector and every hyperbolic partner. Intrinsic abstract
root recognition and the outer bound remain separate obligations.
The actual natural root lines descend injectively to the projective
quotient: a common nonzero fixed vector forces any central scalar
relating two transvections to equal one. Their parameters, cardinalities,
projective labels and conjugation laws are consequently exact.
The natural type-B realization retains the short roots' quadratic
exponential coefficients. The fourth conjugation coefficient is proved
zero on the actual original image before using the source's four-term
root operator. In odd characteristic its scalar commutant and actual
projective image give the original-model comparison. Together with the
characteristic-two root-involution proof, a chain Weyl word proves
even order for every original type-B model. All B tags are removed from
the exact parity residual.
The original G2 Serre model also has a checked rational/integral
representation, obtained by folding the three outer D4 roots. The
short-root polynomial retains its genuine quadratic coefficient. On
the actual representation image a long Weyl word has fourth power one
and is noncentral. Simple projective descent proves even order for
all original simple G2 models. The natural eight-dimensional module
is reducible; the proof uses its actual action image and assumes no
scalar-commutant or named-group recognition assertion. Twisted G2
and other exceptional cases remain explicit in the parity residual.

The soluble-generation extension steps and the bounded binary counting leaf
are also proved here. Importing this file does not replace any outstanding
published input of T1 by an unproved concrete-model assertion.
-/

/-! In characteristic two, restriction of the actual B matrices to their
hyperbolic block is an isomorphism with the literal elementary C group.
The invariant transpose-quadratic form proves its kernel trivial. The
original simple Serre source therefore inherits two-generation, and only
these B tags leave the exact generation residual. Odd-characteristic B
generation remains open at this checkpoint. -/
