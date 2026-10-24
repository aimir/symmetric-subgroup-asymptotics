import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleWeylUnipotentGeneration
import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleTorusInversion
import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleTorusSquareReduction

/-! Whole generation of the literal exceptional-fixed original F4 group
by its actual opposite unipotent subgroups, including field order two.
This does not identify that fixed group with its derived subgroup and
does not assert generation of the original derived-center quotient. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourFixedOppositeGeneration
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourFixedPositiveFamilies
open CFSGReeFFourOppositionFixedPositiveNegative CFSGReeFFourOuterUnipotentGeneration
open CFSGReeFFourMiddleWeylUnipotentGeneration CFSGReeFFourMiddleTorusInversion
open CFSGReeFFourMiddleTorusSquareReduction

theorem oppositeGenerated_eq_top (m : ℕ) : oppositeGenerated m = ⊤ :=
  oppositeGenerated_eq_top_of_middle_inversion m (fixedMiddleWeyl_mem m)
    (middle_fixed_torus_inversion m)

theorem fixed_positive_sup_negative (m : ℕ) :
    fixedPositive m ⊔ fixedNegative m = ⊤ := oppositeGenerated_eq_top m

end SymmetricSubgroupAsymptotics.CFSGReeFFourFixedOppositeGeneration
