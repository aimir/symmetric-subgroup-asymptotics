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
actual image has scalar commutant. Identification with the full classical
symplectic group remains separate.
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

The soluble-generation extension steps and the bounded binary counting leaf
are also proved here. Importing this file does not replace any outstanding
published input of T1 by an unproved concrete-model assertion.
-/
