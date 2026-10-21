import SymmetricSubgroupAsymptotics.CFSGSymplecticRootActionRange

/-! The literal elementary symplectic root parameters are additive,
including both root lengths and characteristic two. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices

theorem elementaryRoot_zero (K : Type) [Field K] (r : ℕ) (neg : Bool) (i : Fin r) :
    elementaryRoot K r neg i 0 = 1 := by
  apply Subtype.ext
  apply Units.ext
  change 1 + (0 : K) • rootMatrix K r neg i = (1 : Mat K r)
  rw [zero_smul, add_zero]

theorem elementaryRoot_add (K : Type) [Field K] (r : ℕ) (neg : Bool) (i : Fin r)
    (a b : K) : elementaryRoot K r neg i (a + b) =
      elementaryRoot K r neg i a * elementaryRoot K r neg i b := by
  apply Subtype.ext
  apply Units.ext
  change 1 + (a + b) • rootMatrix K r neg i =
    (1 + a • rootMatrix K r neg i) * (1 + b • rootMatrix K r neg i)
  simp only [add_smul, mul_add, add_mul, mul_one, one_mul, smul_mul_assoc,
    mul_smul_comm, smul_smul, rootMatrix_sq_zero, smul_zero, add_zero]
  abel

theorem elementaryRoot_inv (K : Type) [Field K] (r : ℕ) (neg : Bool) (i : Fin r) (a : K) :
    (elementaryRoot K r neg i a)⁻¹ = elementaryRoot K r neg i (-a) := by
  apply inv_eq_of_mul_eq_one_right
  rw [← elementaryRoot_add, add_neg_cancel, elementaryRoot_zero]

end SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
