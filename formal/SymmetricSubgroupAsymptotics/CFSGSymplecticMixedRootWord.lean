import SymmetricSubgroupAsymptotics.CFSGSymplecticActualRootStabilizers

/-! An actual mixed-root word and its faithful original action.
For orthogonal v,w it is the symmetric rank-two shear. Its invariance
under w -> w+c*v is proved when 2*b=0, without a characteristic-free
assertion that would fail in odd characteristic. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticTransvectionGeometry
open CFSGSymplecticSerreMatrices
variable {K : Type} [Field K]

def mixedRootWord (r : ℕ) (hr : 0 < r) (v w : Index (r + 1) → K) (b : K) :
    elementaryRootGroup K (r + 1) :=
  actualNaturalRootElement r hr (v + w) b *
    actualNaturalRootElement r hr v (-b) * actualNaturalRootElement r hr w (-b)

theorem mixedRootWord_apply (r : ℕ) (hr : 0 < r)
    (v w : Index (r + 1) → K) (hvw : pairing (r + 1) v w = 0)
    (b : K) (x : Index (r + 1) → K) :
    ((mixedRootWord r hr v w b).val : Mat K (r + 1)) *ᵥ x =
      x + (b * pairing (r + 1) v x) • w + (b * pairing (r + 1) w x) • v := by
  have hwv : pairing (r + 1) w v = 0 := by rw [pairing_swap, hvw, neg_zero]
  change ((((actualNaturalRootElement r hr (v + w) b).val : Mat K (r + 1)) *
    ((actualNaturalRootElement r hr v (-b)).val : Mat K (r + 1))) *
    ((actualNaturalRootElement r hr w (-b)).val : Mat K (r + 1))) *ᵥ x = _
  simp only [← Matrix.mulVec_mulVec, actualNaturalRootElement_apply]
  funext i
  simp only [transvection_apply, pairing_add_left, pairing_add_right,
    pairing_smul_right, pairing_self, hvw, hwv, mul_zero, zero_add, add_zero,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem mixedRootWord_conjugation (r : ℕ) (hr : 0 < r)
    (g : elementaryRootGroup K (r + 1)) (v w : Index (r + 1) → K) (b : K) :
    g * mixedRootWord r hr v w b * g⁻¹ =
      mixedRootWord r hr ((g.val : Mat K (r + 1)) *ᵥ v)
        ((g.val : Mat K (r + 1)) *ᵥ w) b := by
  have he (z : Index (r + 1) → K) (a : K) :
      (MulAut.conj g) (actualNaturalRootElement r hr z a) =
        actualNaturalRootElement r hr ((g.val : Mat K (r + 1)) *ᵥ z) a :=
    actualNaturalRootElement_conjugation r hr g z a
  change (MulAut.conj g) (mixedRootWord r hr v w b) = _
  simp only [mixedRootWord, map_mul, he, Matrix.mulVec_add]

theorem mixedRootWord_add_smul (r : ℕ) (hr : 0 < r)
    (v w : Index (r + 1) → K) (hvw : pairing (r + 1) v w = 0)
    (b c : K) (hb : (2 : K) * b = 0) :
    mixedRootWord r hr v (w + c • v) b = mixedRootWord r hr v w b := by
  have hpair : pairing (r + 1) v (w + c • v) = 0 := by
    rw [pairing_add_right, pairing_smul_right, hvw, pairing_self, mul_zero, add_zero]
  apply elementary_eq_of_mulVec_eq
  intro x
  rw [mixedRootWord_apply r hr v (w + c • v) hpair,
    mixedRootWord_apply r hr v w hvw]
  funext i
  simp only [pairing_add_left, pairing_smul_left, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hextra : (2 : K) * b * c * pairing (r + 1) v x * v i = 0 := by
    rw [hb, zero_mul, zero_mul, zero_mul]
  calc
    _ = (x i + b * pairing (r + 1) v x * w i + b * pairing (r + 1) w x * v i) +
        (2 : K) * b * c * pairing (r + 1) v x * v i := by ring
    _ = _ := by rw [hextra, add_zero]

end SymmetricSubgroupAsymptotics.CFSGSymplecticTransvectionGeometry
