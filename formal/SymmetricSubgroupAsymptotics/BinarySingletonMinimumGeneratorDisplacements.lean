import SymmetricSubgroupAsymptotics.BinaryBooleanFourLeadingDerivativeWords
import SymmetricSubgroupAsymptotics.BinaryBooleanFourKernelLeadingClosure

/-! The four-singleton exception retains the original minimum generators.
A triangular displacement cannot have a nonconstant leading term: actual
derivatives would then cancel another retained generator. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics
open BinaryBooleanFourPolynomialCoordinates BinaryElementaryPairMonomialWidth
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

private theorem smaller_nonzero_has_other_variable : ∀ (i : Fin 4) (b : Fin 16),
    0 < b → b < variableIndex i →
      ∃ j : Fin 4, j ≠ i ∧ support (variableIndex j) ⊆ support b := by decide

variable {A M J : Type} [Ring A] [AddCommGroup M] [Module A M] [Module (ZMod 2) M]

theorem singleton_minimum_generator_displacements_constant
    (C : M →ₗ[ZMod 2] V) (v : Fin 4 → M) (delta : J → A)
    (hnocollision : ∀ i j : Fin 4, i ≠ j → ∀ r : A,
      ¬FiniteRowLeadingWeight.HasLeading (C (r • v i)) (variableIndex j))
    (hderivative : ∀ (i : Fin 4) (z : M) (a : Fin 16),
      FiniteRowLeadingWeight.HasLeading (C z) a → i ∈ support a →
      ∃ r : A, FiniteRowLeadingWeight.HasLeading (C (r • z)) (removeIndex i a))
    (htriangular : ∀ g i (a : Fin 16), variableIndex i ≤ a → C (delta g • v i) a = 0) :
    ∀ g i (a : Fin 16), 0 < a → C (delta g • v i) a = 0 := by
  intro g i a ha
  by_contra hnonzero
  have hf : C (delta g • v i) ≠ 0 := by
    intro he
    exact hnonzero (congrFun he a)
  obtain ⟨b, hb⟩ := FiniteRowLeadingWeight.exists_leading hf
  have hsmall : b < variableIndex i := by
    by_contra h
    exact hb.1 (htriangular g i b (le_of_not_gt h))
  have hpositive : 0 < b := by
    by_contra h
    have he : b = 0 := le_antisymm (le_of_not_gt h) (Fin.zero_le b)
    have hba : b < a := by simpa only [he] using ha
    exact hnonzero (hb.2 a hba)
  obtain ⟨j, hji, hsub⟩ := smaller_nonzero_has_other_variable i b hpositive hsmall
  obtain ⟨r, hr⟩ := exists_operator_leading_subset_of_leading_derivatives C hderivative
    (delta g • v i) b (variableIndex j) hb hsub
  apply hnocollision i j hji.symm (r * delta g)
  simpa only [mul_smul] using hr

end SymmetricSubgroupAsymptotics
