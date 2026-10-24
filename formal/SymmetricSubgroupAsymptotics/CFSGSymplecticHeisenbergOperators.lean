import SymmetricSubgroupAsymptotics.CFSGSymplecticTransvectionGeometry

/-! A uniform Heisenberg operator is a product of three actual natural
transvections. The formulas use no division and hold in every
characteristic. Oddness enters only when the original central parameter
is later mapped to minus twice its value. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGSymplecticHeisenbergOperators

open CFSGSymplecticSerreMatrices CFSGSymplecticTransvectionGeometry
variable {K : Type} [Field K]

def shear (n : ℕ) (e v : Index n → K) (z : K) :
    (Index n → K) ≃ₗ[K] (Index n → K) :=
  transvection n (e + v) 1 * transvection n v (-1) * transvection n e (z - 1)

theorem shear_apply (n : ℕ) (e v x : Index n → K) (z : K)
    (hev : pairing n e v = 0) :
    shear n e v z x = x + pairing n v x • e + pairing n e x • v +
      (z * pairing n e x) • e := by
  have hve : pairing n v e = 0 := by rw [pairing_swap, hev, neg_zero]
  simp only [shear, LinearEquiv.mul_apply, transvection_apply,
    pairing_add_left, pairing_add_right, pairing_smul_right,
    pairing_self, hev, hve, mul_zero, add_zero, zero_add, one_mul]
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem shear_preserves_pairing (n : ℕ) (e v x y : Index n → K) (z : K) :
    pairing n (shear n e v z x) (shear n e v z y) = pairing n x y := by
  simp only [shear, LinearEquiv.mul_apply]
  rw [transvection_preserves_pairing, transvection_preserves_pairing,
    transvection_preserves_pairing]

/-- The alternating cocycle is literal, so no BCH formula or division
by two is involved in this product identity. -/
theorem shear_mul (n : ℕ) (e v w : Index n → K) (z t : K)
    (hev : pairing n e v = 0) (hew : pairing n e w = 0) :
    shear n e v z * shear n e w t =
      shear n e (v + w) (z + t + pairing n v w) := by
  have hve : pairing n v e = 0 := by rw [pairing_swap, hev, neg_zero]
  have hwe : pairing n w e = 0 := by rw [pairing_swap, hew, neg_zero]
  have headd : pairing n e (v + w) = 0 := by rw [pairing_add_right, hev, hew, zero_add]
  apply LinearEquiv.ext
  intro x
  rw [LinearEquiv.mul_apply, shear_apply n e v _ z hev,
    shear_apply n e w x t hew, shear_apply n e (v + w) x _ headd]
  simp only [pairing_add_left, pairing_add_right, pairing_smul_right,
    pairing_self, hev, hew, hve, hwe, mul_zero, add_zero, zero_add]
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem shear_zero_vector (n : ℕ) (e : Index n → K) (z : K) :
    shear n e 0 z = transvection n e z := by
  apply LinearEquiv.ext
  intro x
  rw [shear_apply n e 0 x z (by simp only [pairing_zero_right]), transvection_apply]
  simp only [pairing_zero_left, zero_smul, smul_zero, add_zero]

end SymmetricSubgroupAsymptotics.CFSGSymplecticHeisenbergOperators
