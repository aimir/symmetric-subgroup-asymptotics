import SymmetricSubgroupAsymptotics.CFSGSymplecticHeisenbergWords
import SymmetricSubgroupAsymptotics.CFSGSymplecticNaturalPairingPreservation

/-! Actual elementary conjugation transports the literal shear by its
natural vector action whenever it fixes the first isotropic vector.
This is an equality of actual original elements, not a normalizer or
parabolic recognition premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGSymplecticHeisenbergShearEquivariance

open CFSGSymplecticSerreMatrices CFSGSymplecticTransvectionGeometry
open CFSGSymplecticHeisenbergWords CFSGSymplecticHeisenbergOperators
variable {K : Type} [Field K]

theorem shear_intertwine (n : ℕ) (A : elementaryRootGroup K n)
    (e v x : Index n → K) (z : K)
    (he : (A.val : Mat K n) *ᵥ e = e) (hev : pairing n e v = 0) :
    (A.val : Mat K n) *ᵥ shear n e v z x =
      shear n e ((A.val : Mat K n) *ᵥ v) z ((A.val : Mat K n) *ᵥ x) := by
  have heAv : pairing n e ((A.val : Mat K n) *ᵥ v) = 0 := by
    calc
      _ = pairing n ((A.val : Mat K n) *ᵥ e) ((A.val : Mat K n) *ᵥ v) := by rw [he]
      _ = pairing n e v := elementary_preserves_pairing n A e v
      _ = 0 := hev
  have hpe := elementary_preserves_pairing n A e x
  rw [he] at hpe
  have hpv := elementary_preserves_pairing n A v x
  rw [shear_apply n e v x z hev,
    shear_apply n e ((A.val : Mat K n) *ᵥ v) ((A.val : Mat K n) *ᵥ x) z heAv]
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, he, hpe, hpv]

theorem shearElement_conjugate (m : ℕ) (hm : 0 < m)
    (A : elementaryRootGroup K (m + 1)) (e v : Index (m + 1) → K) (z : K)
    (he : (A.val : Mat K (m + 1)) *ᵥ e = e) (hev : pairing (m + 1) e v = 0) :
    A * shearElement K m hm e v z * A⁻¹ =
      shearElement K m hm e ((A.val : Mat K (m + 1)) *ᵥ v) z := by
  apply (mul_inv_eq_iff_eq_mul).mpr
  apply elementary_ext_of_mulVec K
  intro x
  change (((A.val : Mat K (m + 1)) *
      ((shearElement K m hm e v z).val : Mat K (m + 1))) *ᵥ x) =
    (((shearElement K m hm e ((A.val : Mat K (m + 1)) *ᵥ v) z).val : Mat K (m + 1)) *
      (A.val : Mat K (m + 1))) *ᵥ x
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, shearElement_apply, shearElement_apply]
  exact shear_intertwine (m + 1) A e v x z he hev

end SymmetricSubgroupAsymptotics.CFSGSymplecticHeisenbergShearEquivariance
