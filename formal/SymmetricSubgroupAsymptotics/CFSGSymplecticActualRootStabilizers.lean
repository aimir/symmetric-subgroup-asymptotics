import SymmetricSubgroupAsymptotics.CFSGSymplecticActualNaturalRootLines
import SymmetricSubgroupAsymptotics.CFSGSymplecticRootLineStabilizers

/-! Root-line geometry bound to the SAME original elementary matrix
group. The map-normalizer condition is proved from actual conjugation,
not postulated as an automorphism-recognition input. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticTransvectionGeometry
open CFSGSymplecticSerreMatrices
variable {K : Type} [Field K]

theorem elementary_mulVec_ne_zero (r : ℕ) (g : elementaryRootGroup K r)
    (v : Index r → K) (hv : v ≠ 0) : (g.val : Mat K r) *ᵥ v ≠ 0 := by
  intro hz
  apply hv
  have h := congrArg (fun x : Index r → K => (↑(g.val⁻¹) : Mat K r) *ᵥ x) hz
  change (↑(g.val⁻¹) : Mat K r) *ᵥ ((g.val : Mat K r) *ᵥ v) =
    (↑(g.val⁻¹) : Mat K r) *ᵥ (0 : Index r → K) at h
  rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Matrix.mulVec_zero] at h
  exact h

theorem actualNaturalRootElement_smul (r : ℕ) (hr : 0 < r)
    (v : Index (r + 1) → K) (c a : K) :
    actualNaturalRootElement r hr (c • v) a = actualNaturalRootElement r hr v (a * c ^ 2) := by
  apply elementary_eq_of_mulVec_eq
  intro x
  rw [actualNaturalRootElement_apply, actualNaturalRootElement_apply, transvection_smul]

theorem actualNaturalRootLine_smul (r : ℕ) (hr : 0 < r)
    (v : Index (r + 1) → K) (c : K) (hc : c ≠ 0) :
    actualNaturalRootLine r hr (c • v) = actualNaturalRootLine r hr v := by
  ext T
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨Multiplicative.ofAdd (a.toAdd * c ^ 2), ?_⟩
    exact (actualNaturalRootElement_smul r hr v c a.toAdd).symm
  · rintro ⟨a, rfl⟩
    refine ⟨Multiplicative.ofAdd (a.toAdd / c ^ 2), ?_⟩
    change actualNaturalRootElement r hr (c • v) (a.toAdd / c ^ 2) =
      actualNaturalRootElement r hr v a.toAdd
    rw [actualNaturalRootElement_smul, div_mul_cancel₀ _ (pow_ne_zero 2 hc)]

theorem actualNaturalRootLine_eq_iff (r : ℕ) (hr : 0 < r)
    (v w : Index (r + 1) → K) (hv : v ≠ 0) :
    actualNaturalRootLine r hr v = actualNaturalRootLine r hr w ↔
      ∃ c : K, c ≠ 0 ∧ v = c • w := by
  constructor
  · intro he
    have hm : actualNaturalRootElement r hr v 1 ∈ actualNaturalRootLine r hr v :=
      ⟨Multiplicative.ofAdd 1, rfl⟩
    rw [he] at hm
    obtain ⟨a, ha⟩ := hm
    have hT : transvection (r + 1) v 1 = transvection (r + 1) w a.toAdd := by
      apply LinearEquiv.ext
      intro x
      have h := congrArg (fun g : elementaryRootGroup K (r + 1) => (g.val : Mat K (r + 1)) *ᵥ x) ha.symm
      change ((actualNaturalRootElement r hr v 1).val : Mat K (r + 1)) *ᵥ x =
        ((actualNaturalRootElement r hr w a.toAdd).val : Mat K (r + 1)) *ᵥ x at h
      simpa only [actualNaturalRootElement_apply] using h
    exact transvection_eq_imp_smul (r + 1) v w 1 a.toAdd hv one_ne_zero hT
  · rintro ⟨c, hc, hvc⟩
    rw [hvc]
    exact actualNaturalRootLine_smul r hr w c hc

theorem actualNaturalRootElement_conjugation (r : ℕ) (hr : 0 < r)
    (g : elementaryRootGroup K (r + 1)) (v : Index (r + 1) → K) (a : K) :
    g * actualNaturalRootElement r hr v a * g⁻¹ =
      actualNaturalRootElement r hr ((g.val : Mat K (r + 1)) *ᵥ v) a := by
  apply elementary_eq_of_mulVec_eq
  intro x
  have hi : (g.val : Mat K (r + 1)) *ᵥ ((↑(g.val⁻¹) : Mat K (r + 1)) *ᵥ x) = x := by
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hp := elementary_preserves_pairing (r + 1) g v
    ((↑(g.val⁻¹) : Mat K (r + 1)) *ᵥ x)
  rw [hi] at hp
  change (((g.val : Mat K (r + 1)) *
      ((actualNaturalRootElement r hr v a).val : Mat K (r + 1))) *
      (↑(g.val⁻¹) : Mat K (r + 1))) *ᵥ x = _
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    actualNaturalRootElement_apply, actualNaturalRootElement_apply, transvection_apply,
    Matrix.mulVec_add, Matrix.mulVec_smul, hi]
  change x + (a * pairing (r + 1) v ((↑(g.val⁻¹) : Mat K (r + 1)) *ᵥ x)) •
      ((g.val : Mat K (r + 1)) *ᵥ v) =
    x + (a * pairing (r + 1) ((g.val : Mat K (r + 1)) *ᵥ v) x) •
      ((g.val : Mat K (r + 1)) *ᵥ v)
  rw [← hp]

theorem actualNaturalRootLine_map_conj (r : ℕ) (hr : 0 < r)
    (g : elementaryRootGroup K (r + 1)) (v : Index (r + 1) → K) :
    (actualNaturalRootLine r hr v).map (MulAut.conj g).toMonoidHom =
      actualNaturalRootLine r hr ((g.val : Mat K (r + 1)) *ᵥ v) := by
  ext T
  constructor
  · rintro ⟨S, ⟨a, rfl⟩, hT⟩
    refine ⟨a, ?_⟩
    change actualNaturalRootElement r hr ((g.val : Mat K (r + 1)) *ᵥ v) a.toAdd = T
    change g * actualNaturalRootElement r hr v a.toAdd * g⁻¹ = T at hT
    exact (actualNaturalRootElement_conjugation r hr g v a.toAdd).symm.trans hT
  · rintro ⟨a, rfl⟩
    refine ⟨actualNaturalRootElement r hr v a.toAdd, ⟨a, rfl⟩, ?_⟩
    exact actualNaturalRootElement_conjugation r hr g v a.toAdd

theorem actualNaturalRootLine_normalizer_iff (r : ℕ) (hr : 0 < r)
    (g : elementaryRootGroup K (r + 1)) (v : Index (r + 1) → K) (hv : v ≠ 0) :
    (actualNaturalRootLine r hr v).map (MulAut.conj g).toMonoidHom = actualNaturalRootLine r hr v ↔
      ∃ c : K, c ≠ 0 ∧ (g.val : Mat K (r + 1)) *ᵥ v = c • v := by
  rw [actualNaturalRootLine_map_conj]
  exact actualNaturalRootLine_eq_iff r hr _ v (elementary_mulVec_ne_zero _ g v hv)

end SymmetricSubgroupAsymptotics.CFSGSymplecticTransvectionGeometry
