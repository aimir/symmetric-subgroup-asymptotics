import SymmetricSubgroupAsymptotics.CFSGSymplecticFirstPairStabilizer
import SymmetricSubgroupAsymptotics.CFSGSymplecticHyperbolicPairOrbit
import Mathlib.Tactic.Group

/-! Symplectic elimination on the original coordinates. Once all smaller
form-preserving units are elementary, moving the first hyperbolic pair
and using the faithful literal stabilizer proves the next rank. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticStabilizerCoordinates
open CFSGSymplecticSerreMatrices CFSGSymplecticTransvectionGeometry
variable (K : Type) [Field K]

theorem preservesPairing_mul (r : ℕ) (A B : Mat K r)
    (hA : PreservesPairing r A) (hB : PreservesPairing r B) :
    PreservesPairing r (A * B) := by
  intro v w
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hA, hB]

theorem preservesPairing_inv (r : ℕ) (u : (Mat K r)ˣ)
    (hu : PreservesPairing r (u : Mat K r)) :
    PreservesPairing r (↑(u⁻¹) : Mat K r) := by
  intro v w
  have h := hu ((↑(u⁻¹) : Mat K r) *ᵥ v) ((↑(u⁻¹) : Mat K r) *ᵥ w)
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Units.mul_inv,
    Matrix.one_mulVec, Matrix.one_mulVec] at h
  exact h.symm

theorem all_formPreserving_elementary_step (r : ℕ) (hr : 0 < r)
    (hsmall : ∀ u : (Mat K r)ˣ, PreservesPairing r (u : Mat K r) →
      u ∈ elementaryRootGroup K r)
    (u : (Mat K (r + 1))ˣ) (hu : PreservesPairing (r + 1) (u : Mat K (r + 1))) :
    u ∈ elementaryRootGroup K (r + 1) := by
  let e : Index (r + 1) → K := Pi.single (Sum.inl 0) 1
  let f : Index (r + 1) → K := Pi.single (Sum.inr 0) 1
  have he : e ≠ 0 := by
    intro h
    have h' := congrFun h (Sum.inl 0)
    simpa [e] using h'
  have hue : (u : Mat K (r + 1)) *ᵥ e ≠ 0 := by
    intro h
    apply he
    apply Matrix.mulVec_injective_of_isUnit u.isUnit
    simpa only [Matrix.mulVec_zero] using h
  obtain ⟨a, ha⟩ := exists_elementary_mulVec_first_basis K r hr
    ((u : Mat K (r + 1)) *ᵥ e) hue
  let v : (Mat K (r + 1))ˣ := a.val⁻¹ * u
  have hve : (v : Mat K (r + 1)) *ᵥ e = e := by
    change ((↑(a.val⁻¹) : Mat K (r + 1)) * (u : Mat K (r + 1))) *ᵥ e = e
    rw [← Matrix.mulVec_mulVec, ← ha, Matrix.mulVec_mulVec,
      Units.inv_mul, Matrix.one_mulVec]
  have hAp : PreservesPairing (r + 1) (a.val : Mat K (r + 1)) :=
    elementary_preserves_pairing (r + 1) a
  have hv : PreservesPairing (r + 1) (v : Mat K (r + 1)) :=
    preservesPairing_mul K (r + 1) _ _ (preservesPairing_inv K (r + 1) a.val hAp) hu
  have hef : pairing (r + 1) e f = 1 := by simp [e, f, pairing_neg_basis]
  have hevf : pairing (r + 1) e ((v : Mat K (r + 1)) *ᵥ f) = 1 := by
    have h := hv e f
    rw [hve, hef] at h
    exact h
  obtain ⟨b, hbe, hbf⟩ := exists_elementary_fix_hyperbolic_partner r hr e f
    ((v : Mat K (r + 1)) *ᵥ f) hef hevf
  let k : (Mat K (r + 1))ˣ := b.val * v
  have hk : FixesFirstPair r (k : Mat K (r + 1)) := by
    constructor
    · change ((b.val : Mat K (r + 1)) * (v : Mat K (r + 1))) *ᵥ e = e
      rw [← Matrix.mulVec_mulVec, hve, hbe]
    · change ((b.val : Mat K (r + 1)) * (v : Mat K (r + 1))) *ᵥ f = f
      rw [← Matrix.mulVec_mulVec, hbf]
  have hkp : PreservesPairing (r + 1) (k : Mat K (r + 1)) :=
    preservesPairing_mul K (r + 1) _ _ (elementary_preserves_pairing (r + 1) b) hv
  have htail : tailUnits r k hk ∈ elementaryRootGroup K r :=
    hsmall _ (tailUnits_preserves_pairing r k hk hkp)
  obtain ⟨c, hc⟩ := elementaryRootGroup_le_firstPairTail_range K r htail
  have hceq : k = c.val := by
    apply Units.ext
    apply eq_of_same_tail r _ _ hkp ?_ hk c.property.2
    · exact congrArg (fun z : (Mat K r)ˣ => (z : Mat K r)) hc.symm
    · exact preservesPairing_of_form (r + 1) _
        (elementaryRootGroup_le_formPreserving K (r + 1) c.property.1)
  have hkmem : k ∈ elementaryRootGroup K (r + 1) := hceq ▸ c.property.1
  have heq : u = a.val * b.val⁻¹ * k := by dsimp [k, v]; group
  rw [heq]
  exact (elementaryRootGroup K (r + 1)).mul_mem
    ((elementaryRootGroup K (r + 1)).mul_mem a.property
      ((elementaryRootGroup K (r + 1)).inv_mem b.property)) hkmem

end SymmetricSubgroupAsymptotics.CFSGSymplecticStabilizerCoordinates
