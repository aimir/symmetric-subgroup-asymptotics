import SymmetricSubgroupAsymptotics.AlgebraOperatorLeadingGeneratorBound
import SymmetricSubgroupAsymptotics.BinaryMonomialRaisingWords

/-! The common-shear leading paths produce six genuine module generators.
Concrete applications supply each step by an operator in their original
group algebra; no additional classification or capacity input is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

open BinaryMonomialRaisingWords
open BinaryElementaryPairMonomialWidth
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

variable {A M : Type} [Ring A] [Algebra (ZMod 2) A]
    [AddCommGroup M] [Module A M] [Module (ZMod 2) M]
    [IsScalarTower (ZMod 2) A M] {d : ℕ}

theorem binary_generating_finset_le_six_of_common_shear_steps
    (hd : ModuleGeneratedBy A M d) (C : M →ₗ[ZMod 2] (Fin 32 → ZMod 2))
    (hC : Function.Injective C)
    (hstep : ∀ op a b, BinaryMonomialRaisingWords.step op a = some b →
      ∀ v : M, FiniteRowLeadingWeight.HasLeading (C v) (index a) →
        ∃ r : A, FiniteRowLeadingWeight.HasLeading (C (r • v)) (index b)) :
    ∃ S : Finset M, Submodule.span A (S : Set M) = ⊤ ∧ S.card ≤ 6 := by
  apply algebra_generating_finset_le_of_operator_leading_width hd C hC 0
    RaisesIndex raisesIndex_refl _ 6 antichain_index_card_le_six
  intro v a b hv hr
  obtain ⟨r, hraise⟩ := ModuleLeadingOperatorWords.exists_operator_of_run
    BinaryMonomialRaisingWords.step
    (fun v label => FiniteRowLeadingWeight.HasLeading (C v) (index label))
    hstep (path (index.symm a) (index.symm b)) (index.symm a) (index.symm b)
    (path_valid _ _ hr) v (by simpa only [Equiv.apply_symm_apply] using hv)
  exact ⟨r, by simpa only [Equiv.apply_symm_apply] using hraise⟩

end SymmetricSubgroupAsymptotics
