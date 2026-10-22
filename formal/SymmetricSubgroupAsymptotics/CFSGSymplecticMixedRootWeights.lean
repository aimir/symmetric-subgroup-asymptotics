import SymmetricSubgroupAsymptotics.CFSGSymplecticMixedRootWord

/-! Actual mixed-root weights under the first two flag coordinates.
The doubled shear term is retained until its parameter is proved zero. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticTransvectionGeometry
open CFSGSymplecticSerreMatrices
variable {K : Type} [Field K]

theorem mixedRootWord_two_weights (r : ℕ) (hr : 0 < r)
    (v w : Index (r + 1) → K) (hvw : pairing (r + 1) v w = 0)
    (a b c t : K) (ht : (2 : K) * t = 0) :
    mixedRootWord r hr (a • v) (b • w + c • v) t =
      mixedRootWord r hr v w (t * a * b) := by
  have hpair : pairing (r + 1) (a • v) (b • w + c • v) = 0 := by
    rw [pairing_smul_left, pairing_add_right, pairing_smul_right,
      pairing_smul_right, hvw, pairing_self]
    ring
  apply elementary_eq_of_mulVec_eq
  intro x
  rw [mixedRootWord_apply r hr (a • v) (b • w + c • v) hpair,
    mixedRootWord_apply r hr v w hvw]
  funext i
  simp only [pairing_add_left, pairing_smul_left, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hextra : (2 : K) * t * a * c * pairing (r + 1) v x * v i = 0 := by
    rw [ht, zero_mul, zero_mul, zero_mul, zero_mul]
  calc
    _ = (x i + t * a * b * pairing (r + 1) v x * w i +
        t * a * b * pairing (r + 1) w x * v i) +
        (2 : K) * t * a * c * pairing (r + 1) v x * v i := by ring
    _ = _ := by rw [hextra, add_zero]

end SymmetricSubgroupAsymptotics.CFSGSymplecticTransvectionGeometry
