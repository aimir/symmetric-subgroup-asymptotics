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
also supplies its exact order and normalizer intersection. Shared integral
Serre divided-power and local-nilpotence lemmas support further Lie families;
every displayed root operator now has a checked invertible lift, including
after integral base change. These facts do not assert additive root
parameters, cross-root relations or the uniform finite-type nilpotence bound.

The soluble-generation extension steps and the bounded binary counting leaf
are also proved here. Importing this file does not replace any outstanding
published input of T1 by an unproved concrete-model assertion.
-/
