import SymmetricSubgroupAsymptotics.AlgebraOperatorLeadingGeneratorBound
import SymmetricSubgroupAsymptotics.BinaryFiveQuadraticRaisingWords

/-! Five-quadratic leading paths produce seven genuine module generators.
Concrete applications supply each step by an operator in their original
group algebra; no additional classification or capacity input is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

open BinaryMonomialRaisingWords (index path)
open BinaryFiveQuadraticRaisingWords
open BinaryElementaryPairMonomialWidth
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

variable {A M : Type} [Ring A] [Algebra (ZMod 2) A]
    [AddCommGroup M] [Module A M] [Module (ZMod 2) M]
    [IsScalarTower (ZMod 2) A M] {d : ℕ}

theorem binary_generating_finset_le_seven_of_five_quadratic_steps
    (j : Fin 6) (hd : ModuleGeneratedBy A M d) (C : M →ₗ[ZMod 2] (Fin 32 → ZMod 2))
    (hC : Function.Injective C)
    (hstep : ∀ op a b, BinaryFiveQuadraticRaisingWords.step j op a = some b →
      ∀ v : M, FiniteRowLeadingWeight.HasLeading (C v) (index a) →
        ∃ r : A, FiniteRowLeadingWeight.HasLeading (C (r • v)) (index b)) :
    ∃ S : Finset M, Submodule.span A (S : Set M) = ⊤ ∧ S.card ≤ 7 := by
  apply algebra_generating_finset_le_of_operator_leading_width hd C hC 0
    (RaisesIndex j) (raisesIndex_refl j) _ 7 (antichain_index_card_le_seven j)
  intro v a b hv hr
  obtain ⟨r, hraise⟩ := ModuleLeadingOperatorWords.exists_operator_of_run
    (BinaryFiveQuadraticRaisingWords.step j)
    (fun v label => FiniteRowLeadingWeight.HasLeading (C v) (index label))
    hstep (path (index.symm a) (index.symm b)) (index.symm a) (index.symm b)
    (path_valid j _ _ hr) v (by simpa only [Equiv.apply_symm_apply] using hv)
  exact ⟨r, by simpa only [Equiv.apply_symm_apply] using hraise⟩

end SymmetricSubgroupAsymptotics
