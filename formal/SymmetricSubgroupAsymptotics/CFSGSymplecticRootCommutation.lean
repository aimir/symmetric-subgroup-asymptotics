import SymmetricSubgroupAsymptotics.CFSGSymplecticProjectiveNaturalRootLines
import SymmetricSubgroupAsymptotics.CFSGLinearFunctionalKernels
import Mathlib.Algebra.Group.Commute.Hom

/-! Commuting natural-root tests recover the original projective
vector line, both before and after the actual central quotient.
The central quotient does not create extra commuting root pairs. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticTransvectionGeometry
open CFSGSymplecticSerreMatrices
variable {K : Type} [Field K]

theorem actualNaturalRootElement_commute_iff (r : ℕ) (hr : 0 < r)
    (v w : Index (r + 1) → K) (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    Commute (actualNaturalRootElement r hr v a) (actualNaturalRootElement r hr w b) ↔
      pairing (r + 1) v w = 0 := by
  rw [← transvection_commute_iff (r + 1) v w a b ha hb]
  constructor
  · intro h
    change transvection (r + 1) v a * transvection (r + 1) w b =
      transvection (r + 1) w b * transvection (r + 1) v a
    apply LinearEquiv.ext
    intro x
    have he := congrArg (fun g : elementaryRootGroup K (r + 1) =>
      (g.val : Mat K (r + 1)) *ᵥ x) h.eq
    change (((actualNaturalRootElement r hr v a).val : Mat K (r + 1)) *
      ((actualNaturalRootElement r hr w b).val : Mat K (r + 1))) *ᵥ x =
      (((actualNaturalRootElement r hr w b).val : Mat K (r + 1)) *
      ((actualNaturalRootElement r hr v a).val : Mat K (r + 1))) *ᵥ x at he
    simpa only [← Matrix.mulVec_mulVec, actualNaturalRootElement_apply,
      LinearEquiv.mul_apply] using he
  · intro h
    change actualNaturalRootElement r hr v a * actualNaturalRootElement r hr w b =
      actualNaturalRootElement r hr w b * actualNaturalRootElement r hr v a
    apply elementary_eq_of_mulVec_eq
    intro x
    change (((actualNaturalRootElement r hr v a).val : Mat K (r + 1)) *
      ((actualNaturalRootElement r hr w b).val : Mat K (r + 1))) *ᵥ x =
      (((actualNaturalRootElement r hr w b).val : Mat K (r + 1)) *
      ((actualNaturalRootElement r hr v a).val : Mat K (r + 1))) *ᵥ x
    simpa only [← Matrix.mulVec_mulVec, actualNaturalRootElement_apply,
      LinearEquiv.mul_apply] using congrArg
        (fun T : (Index (r + 1) → K) ≃ₗ[K] (Index (r + 1) → K) => T x) h.eq

theorem projectiveNaturalRootElement_commute_iff (r : ℕ) (hr : 0 < r)
    (v w : Index (r + 1) → K) (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    Commute (projectiveNaturalRootHom r hr v (Multiplicative.ofAdd a))
      (projectiveNaturalRootHom r hr w (Multiplicative.ofAdd b)) ↔
      pairing (r + 1) v w = 0 := by
  let q := QuotientGroup.mk' (Subgroup.center (elementaryRootGroup K (r + 1)))
  constructor
  · intro h
    have he : q (actualNaturalRootElement r hr v a *
        actualNaturalRootElement r hr w b * (actualNaturalRootElement r hr v a)⁻¹) =
        q (actualNaturalRootElement r hr w b) := by
      change q (actualNaturalRootElement r hr v a) * q (actualNaturalRootElement r hr w b) =
        q (actualNaturalRootElement r hr w b) * q (actualNaturalRootElement r hr v a) at h
      rw [map_mul, map_mul, map_inv, h, mul_assoc, mul_inv_cancel, mul_one]
    rw [actualNaturalRootElement_conjugation] at he
    have hlift := actualNaturalRootElement_eq_of_projective_eq r hr
      (((actualNaturalRootElement r hr v a).val : Mat K (r + 1)) *ᵥ w) w b b he
    have hcomm : Commute (actualNaturalRootElement r hr v a)
        (actualNaturalRootElement r hr w b) := by
      change actualNaturalRootElement r hr v a * actualNaturalRootElement r hr w b =
        actualNaturalRootElement r hr w b * actualNaturalRootElement r hr v a
      calc
        _ = (actualNaturalRootElement r hr v a * actualNaturalRootElement r hr w b *
            (actualNaturalRootElement r hr v a)⁻¹) * actualNaturalRootElement r hr v a := by
          simp only [mul_assoc, inv_mul_cancel, mul_one]
        _ = _ := by rw [actualNaturalRootElement_conjugation, hlift]
    exact (actualNaturalRootElement_commute_iff r hr v w a b ha hb).mp hcomm
  · intro h
    exact ((actualNaturalRootElement_commute_iff r hr v w a b ha hb).mpr h).map q

theorem same_pairing_zero_tests_iff (r : ℕ) (v w : Index r → K) (hv : v ≠ 0) :
    (∀ x, pairing r v x = 0 ↔ pairing r w x = 0) ↔
      ∃ c : K, c ≠ 0 ∧ v = c • w := by
  constructor
  · intro h
    have hf : pairingDual r v ≠ 0 := by
      obtain ⟨x, hx⟩ := exists_pairing_ne_zero r v hv
      intro hz
      exact hx (congrArg (fun f : Module.Dual K (Index r → K) => f x) hz)
    obtain ⟨c, hc, he⟩ := CFSGLinearFunctionalKernels.nonzero_smul_of_zero_iff
      (pairingDual r v) (pairingDual r w) hf h
    refine ⟨c, hc, ?_⟩
    funext i
    cases i with
    | inl i =>
      have hx := congrArg (fun f : Module.Dual K (Index r → K) =>
        f (Pi.single (Sum.inr i) 1)) he
      change pairing r v (Pi.single (Sum.inr i) 1) =
        c * pairing r w (Pi.single (Sum.inr i) 1) at hx
      simpa only [pairing_neg_basis, Pi.smul_apply, smul_eq_mul] using hx
    | inr i =>
      have hx := congrArg (fun f : Module.Dual K (Index r → K) =>
        f (Pi.single (Sum.inl i) 1)) he
      change pairing r v (Pi.single (Sum.inl i) 1) =
        c * pairing r w (Pi.single (Sum.inl i) 1) at hx
      have hh : -v (Sum.inr i) = -(c * w (Sum.inr i)) := by
        simpa only [pairing_pos_basis, mul_neg] using hx
      exact neg_injective hh
  · rintro ⟨c, hc, rfl⟩ x
    rw [pairing_smul_left]
    exact mul_eq_zero.trans (or_iff_right hc)

theorem projective_root_line_eq_iff_commuting_tests (r : ℕ) (hr : 0 < r)
    (v w : Index (r + 1) → K) (hv : v ≠ 0) :
    projectiveNaturalRootLine r hr v = projectiveNaturalRootLine r hr w ↔
      ∀ x : Index (r + 1) → K,
        (Commute (projectiveNaturalRootHom r hr v (Multiplicative.ofAdd 1))
          (projectiveNaturalRootHom r hr x (Multiplicative.ofAdd 1)) ↔
        Commute (projectiveNaturalRootHom r hr w (Multiplicative.ofAdd 1))
          (projectiveNaturalRootHom r hr x (Multiplicative.ofAdd 1))) := by
  simp only [projectiveNaturalRootElement_commute_iff r hr _ _ (1 : K) 1
    one_ne_zero one_ne_zero]
  rw [projectiveNaturalRootLine_eq_iff r hr v w hv,
    same_pairing_zero_tests_iff (r + 1) v w hv]

end SymmetricSubgroupAsymptotics.CFSGSymplecticTransvectionGeometry
