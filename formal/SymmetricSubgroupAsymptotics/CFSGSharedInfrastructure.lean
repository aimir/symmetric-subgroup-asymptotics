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

The soluble-generation extension steps and the bounded binary counting leaf
are also proved here. Importing this file does not replace any outstanding
published input of T1 by an unproved concrete-model assertion.
-/
