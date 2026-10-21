import SymmetricSubgroupAsymptotics.CFSGSymplecticCartanMatrices
import SymmetricSubgroupAsymptotics.CFSGSymplecticSerreEF

/-! Integer coroot weights of the actual symplectic simple-root supports,
in the pinned C-transpose convention. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices

def weight (r : ℕ) (i : Fin r) (x : Index r) : ℤ := cartan ℤ r i x x

theorem weight_inr (r : ℕ) (i j : Fin r) :
    weight r i (Sum.inr j) = -weight r i (Sum.inl j) := by
  by_cases hi : i.val + 1 < r
  · simp [weight, cartan_eq, hi, Matrix.single, neg_sub]
  · simp [weight, cartan_eq, hi, Matrix.single]

theorem weight_inl_eq (r : ℕ) (i j : Fin r) :
    weight r i (Sum.inl j) =
      if i.val + 1 < r then
        (if i.val = j.val then 1 else 0) - (if i.val + 1 = j.val then 1 else 0)
      else if i.val = j.val then 1 else 0 := by
  by_cases hi : i.val + 1 < r <;>
    simp [weight, cartan_eq, hi, Matrix.single, Fin.ext_iff]

theorem weight_chain (r : ℕ) (i j : Fin r) (hj : j.val + 1 < r) :
    weight r i (Sum.inl j) - weight r i (Sum.inl (⟨j.val + 1, hj⟩ : Fin r)) =
      CartanMatrix.B r i j := by
  have hiLt := i.isLt
  have hjLt := j.isLt
  simp only [weight_inl_eq, CartanMatrix.B, Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> omega

theorem weight_chain_mirror (r : ℕ) (i j : Fin r) (hj : j.val + 1 < r) :
    weight r i (Sum.inr (⟨j.val + 1, hj⟩ : Fin r)) - weight r i (Sum.inr j) =
      CartanMatrix.B r i j := by
  rw [weight_inr, weight_inr]
  have h := weight_chain r i j hj
  omega

theorem weight_terminal (r : ℕ) (i j : Fin r) (hj : ¬j.val + 1 < r) :
    weight r i (Sum.inl j) - weight r i (Sum.inr j) = CartanMatrix.B r i j := by
  have hiLt := i.isLt
  have hjLt := j.isLt
  have hlast : j.val + 1 = r := by omega
  rw [weight_inr]
  simp only [weight_inl_eq, CartanMatrix.B, Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> omega

end SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
