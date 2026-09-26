import SymmetricSubgroupAsymptotics.BinaryCarrierQuotient8T26Normal3
import SymmetricSubgroupAsymptotics.PrimeEvaluationKernelGenerators

/-! The prime-two evaluation kernel of the literal original 8T26 group.
Each square of the original ordered three-generator tuple is identified
pointwise with one of the already checked eight derived rows. No normal
registry, structural profile, or replacement action is assumed. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryCarrierEvaluationKernel8T26

open BinaryCarrierRank8T26Normal3 BinaryCarrierQuotient8T26Normal3

abbrev Original := Subgroup.closure (Set.range BinaryMenuCayley8T26.generators)

/-- Only three original generators, eight existing derived rows and
the eight original points occur in this finite equation. -/
theorem generator_squares_pointwise : ∀ i : Fin 3, ∃ r : Fin 8, ∀ a : Fin 8,
    BinaryMenuCayley8T26.generators i (BinaryMenuCayley8T26.generators i a) =
      (derivedRows r : Equiv.Perm (Fin 8)) a := by
  decide +kernel

theorem generator_square_mem_D (i : Fin 3) : originalGenerators i ^ 2 ∈ D := by
  obtain ⟨r, hr⟩ := generator_squares_pointwise i
  have he : originalGenerators i ^ 2 = derivedRows r := by
    apply Subtype.ext
    apply Equiv.ext
    intro a
    change (BinaryMenuCayley8T26.generators i ^ 2) a = _
    simpa only [pow_two, Equiv.Perm.mul_apply] using hr a
  rw [he]
  exact derivedRows_mem r

theorem generator_square_mem_commutator (i : Fin 3) :
    originalGenerators i ^ 2 ∈ commutator Original := by
  rw [derived_eq]
  exact generator_square_mem_D i

/-- Equality of actual subgroups of the original literal closure. -/
theorem evaluationKernel_eq_commutator :
    (primeAbelianizationGroupMap 2 Original).ker = commutator Original :=
  primeAbelianizationGroupMap_ker_eq_commutator_of_generator_powers 2
    originalGenerators originalGenerators_full generator_square_mem_commutator

end SymmetricSubgroupAsymptotics.BinaryCarrierEvaluationKernel8T26
