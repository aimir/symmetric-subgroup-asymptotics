import SymmetricSubgroupAsymptotics.CFSGSymplecticTransvectionGeometry
import SymmetricSubgroupAsymptotics.CFSGSymplecticFirstLowerLongRoot

/-! The new natural transvection geometry contains the SAME actual
upper/lower long-root matrices of the original elementary model. This
is an explicit original-action identity, not a model recognition premise. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticTransvectionGeometry
open CFSGSymplecticSerreMatrices
variable {K : Type} [Field K]

theorem pairing_pos_basis_left (r : ℕ) (x : Index r → K) (i : Fin r) :
    pairing r (Pi.single (Sum.inl i) 1) x = x (Sum.inr i) := by
  rw [pairing_swap, pairing_pos_basis]
  exact neg_neg _

theorem pairing_neg_basis_left (r : ℕ) (x : Index r → K) (i : Fin r) :
    pairing r (Pi.single (Sum.inr i) 1) x = -x (Sum.inl i) := by
  rw [pairing_swap, pairing_neg_basis]

theorem firstLongRoot_mulVec_eq_transvection (r : ℕ) (a : K) (x : Index (r + 1) → K) :
    ((firstLongRoot K r a).val : Mat K (r + 1)) *ᵥ x =
      transvection (r + 1) (Pi.single (Sum.inl (0 : Fin (r + 1))) 1) a x := by
  rw [firstLongRoot_coe]
  simp only [Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec,
    transvection_apply, pairing_pos_basis_left]
  funext j
  simp [Function.update_apply, Pi.single_apply, eq_comm]

theorem firstLowerLongRoot_mulVec_eq_transvection (r : ℕ) (a : K) (x : Index (r + 1) → K) :
    ((firstLowerLongRoot K r a).val : Mat K (r + 1)) *ᵥ x =
      transvection (r + 1) (Pi.single (Sum.inr (0 : Fin (r + 1))) 1) (-a) x := by
  rw [firstLowerLongRoot_coe]
  simp only [Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec,
    transvection_apply, pairing_neg_basis_left, neg_mul_neg]
  funext j
  simp [Function.update_apply, Pi.single_apply, eq_comm]

end SymmetricSubgroupAsymptotics.CFSGSymplecticTransvectionGeometry
