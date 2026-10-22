import SymmetricSubgroupAsymptotics.CFSGOrthogonalBSingularVectorCount
import Mathlib.Data.Fintype.Card

/-! Nonzero singular vectors of the SAME original B Gram cone. Only
its zero vector is removed from the checked exact vector count. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBNonzeroSingularCount
open CFSGOrthogonalBSerreMatrices
variable (K : Type) [Field K]

abbrev NonzeroCone (n : ℕ) :=
  {v : Index n → K // (gram K n).toBilin' v v = 0 ∧ v ≠ 0}

def nonzeroConeEquiv (n : ℕ) : NonzeroCone K n ≃
    {v : {x : Index n → K // (gram K n).toBilin' x x = 0} //
      v ≠ (⟨0, by simp⟩ : {x : Index n → K // (gram K n).toBilin' x x = 0})} where
  toFun v := ⟨⟨v.val, v.property.1⟩, fun he => v.property.2 (congrArg Subtype.val he)⟩
  invFun v := ⟨v.val.val, v.val.property, fun he => v.property (Subtype.ext he)⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem nonzero_singular_card [Finite K] (n : ℕ) (h2 : (2 : K) ≠ 0) :
    Nat.card (NonzeroCone K n) = Nat.card K ^ (2 * n) - 1 := by
  classical
  let Cone := {x : Index n → K // (gram K n).toBilin' x x = 0}
  let z : Cone := ⟨0, by simp⟩
  letI : Fintype Cone := Fintype.ofFinite Cone
  calc
    Nat.card (NonzeroCone K n) = Nat.card {v : Cone // v ≠ z} :=
      Nat.card_congr (nonzeroConeEquiv K n)
    _ = Nat.card Cone - 1 := by
      simp only [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq]
    _ = Nat.card K ^ (2 * n) - 1 := by
      rw [CFSGOrthogonalBSingularVectorCount.singular_vectors_card K n h2]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBNonzeroSingularCount
