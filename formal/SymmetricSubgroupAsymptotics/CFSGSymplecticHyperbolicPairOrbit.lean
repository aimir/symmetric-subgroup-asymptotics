import SymmetricSubgroupAsymptotics.CFSGSymplecticAllNaturalTransvections

/-! Actual elementary words move the second vector of a hyperbolic
pair while fixing its first vector. This is the first stabilizer step
in symplectic elimination, not an abstract automorphism-recognition
assumption. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticTransvectionGeometry
open CFSGSymplecticSerreMatrices
variable {K : Type} [Field K]

theorem pairing_neg_left (r : ℕ) (v w : Index r → K) :
    pairing r (-v) w = -pairing r v w := by
  rw [show -v = (-1 : K) • v by simp, pairing_smul_left]
  simp

theorem pairing_neg_right (r : ℕ) (v w : Index r → K) :
    pairing r v (-w) = -pairing r v w := by
  rw [show -w = (-1 : K) • w by simp, pairing_smul_right]
  simp

theorem exists_elementary_fix_move (r : ℕ) (hr : 0 < r)
    (e u v : Index (r + 1) → K)
    (he : pairing (r + 1) e u = pairing (r + 1) e v)
    (hvu : pairing (r + 1) v u ≠ 0) :
    ∃ g : elementaryRootGroup K (r + 1),
      (g.val : Mat K (r + 1)) *ᵥ e = e ∧ (g.val : Mat K (r + 1)) *ᵥ u = v := by
  have hd : v - u ≠ 0 := by
    intro hz
    have hv := sub_eq_zero.mp hz
    exact hvu (by rw [hv, pairing_self])
  have hdu : pairing (r + 1) (v - u) u = pairing (r + 1) v u := by
    simp only [sub_eq_add_neg, pairing_add_left, pairing_neg_left, pairing_self, neg_zero, add_zero]
  have hde : pairing (r + 1) (v - u) e = 0 := by
    simp only [sub_eq_add_neg, pairing_add_left, pairing_neg_left]
    rw [pairing_swap (r + 1) v e, pairing_swap (r + 1) u e, he]
    ring
  obtain ⟨g, hg⟩ := exists_elementary_natural_transvection r hr (v - u) hd
    (pairing (r + 1) v u)⁻¹
  refine ⟨g, ?_, ?_⟩
  · rw [hg, transvection_apply, hde, mul_zero, zero_smul, add_zero]
  · rw [hg, transvection_apply, hdu, inv_mul_cancel₀ hvu, one_smul]
    abel

theorem exists_elementary_fix_hyperbolic_partner (r : ℕ) (hr : 0 < r)
    (e f w : Index (r + 1) → K)
    (hef : pairing (r + 1) e f = 1) (hew : pairing (r + 1) e w = 1) :
    ∃ g : elementaryRootGroup K (r + 1),
      (g.val : Mat K (r + 1)) *ᵥ e = e ∧ (g.val : Mat K (r + 1)) *ᵥ w = f := by
  by_cases hfw : pairing (r + 1) f w = 0
  · have he' : pairing (r + 1) e (f + e) = 1 := by
      rw [pairing_add_right, hef, pairing_self, add_zero]
    have hneww : pairing (r + 1) (f + e) w ≠ 0 := by
      rw [pairing_add_left, hfw, hew, zero_add]
      exact one_ne_zero
    have hfnew : pairing (r + 1) f (f + e) ≠ 0 := by
      rw [pairing_add_right, pairing_self, pairing_swap (r + 1) f e, hef, zero_add]
      exact neg_ne_zero.mpr one_ne_zero
    obtain ⟨a, hae, haw⟩ := exists_elementary_fix_move r hr e w (f + e) (hew.trans he'.symm) hneww
    obtain ⟨b, hbe, hbf⟩ := exists_elementary_fix_move r hr e (f + e) f (he'.trans hef.symm) hfnew
    refine ⟨b * a, ?_, ?_⟩
    · change ((b.val : Mat K (r + 1)) * (a.val : Mat K (r + 1))) *ᵥ e = e
      rw [← Matrix.mulVec_mulVec, hae, hbe]
    · change ((b.val : Mat K (r + 1)) * (a.val : Mat K (r + 1))) *ᵥ w = f
      rw [← Matrix.mulVec_mulVec, haw, hbf]
  · exact exists_elementary_fix_move r hr e w f (hew.trans hef.symm) hfw

end SymmetricSubgroupAsymptotics.CFSGSymplecticTransvectionGeometry
