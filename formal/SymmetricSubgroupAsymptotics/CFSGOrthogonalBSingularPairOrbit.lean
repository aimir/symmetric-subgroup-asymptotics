import SymmetricSubgroupAsymptotics.CFSGOrthogonalBTailSingularOrbit
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBSingularRootPlanes

/-! Actual original B root words put every independent, mutually
orthogonal singular pair into the standard positive two-plane. No
polar-space transitivity assumption or full-group recognition occurs. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBVectorCoordinates
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBUnipotent CFSGOrthogonalBTailCoordinates
variable (K : Type) [Field K]

theorem exists_singular_pair_frame (h2 : (2 : K) ≠ 0) (s : ℕ)
    (v w : Index (s + 3) → K) (hv : v ≠ 0)
    (hsv : (gram K (s + 3)).toBilin' v v = 0)
    (hsw : (gram K (s + 3)).toBilin' w w = 0)
    (hvw : (gram K (s + 3)).toBilin' v w = 0)
    (hnot : ∀ c : K, w ≠ c • v) :
    ∃ g : elementaryRootGroup K (s + 3), ∃ c : K,
      (g.val : Mat K (s + 3)) *ᵥ v = Pi.single (pos (s + 3) 0) 1 ∧
      (g.val : Mat K (s + 3)) *ᵥ w = c • Pi.single (pos (s + 3) 0) 1 +
        Pi.single (pos (s + 3) (secondIndex s)) 1 := by
  obtain ⟨g0, hg0⟩ := exists_normalize_singular K h2 (s + 1) v hv hsv
  let w0 := (g0.val : Mat K (s + 3)) *ᵥ w
  have hp : (gram K (s + 3)).toBilin' (Pi.single (pos (s + 3) 0) 1) w0 = 0 := by
    rw [← hg0]
    exact (natural_pairing_invariant h2 (s + 3) g0 v w).trans hvw
  have hn : w0 (neg (s + 3) 0) = 0 := by
    have he : (2 : K) * w0 (neg (s + 3) 0) = 0 :=
      (pairing_first_positive K (s + 2) w0).symm.trans hp
    exact (mul_eq_zero.mp he).resolve_left h2
  have hw0s : (gram K (s + 3)).toBilin' w0 w0 = 0 :=
    (natural_pairing_invariant h2 (s + 3) g0 w w).trans hsw
  have ht : tailRestriction K (s + 2) w0 ≠ 0 := by
    intro hz
    have he := vector_eq_first_of_tail_zero K (s + 2) w0 hz hn
    have hb := congrArg (fun x : Index (s + 3) → K => (↑(g0.val⁻¹) : Mat K (s + 3)) *ᵥ x) he
    change (↑(g0.val⁻¹) : Mat K (s + 3)) *ᵥ ((g0.val : Mat K (s + 3)) *ᵥ w) =
      (↑(g0.val⁻¹) : Mat K (s + 3)) *ᵥ
        (w0 (pos (s + 3) 0) • Pi.single (pos (s + 3) 0) 1) at hb
    rw [← hg0] at hb
    simp only [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at hb
    exact hnot _ hb
  obtain ⟨t, ht0, htw⟩ := exists_tail_normalize_singular K h2 s w0 hn ht hw0s
  refine ⟨t * g0, w0 (pos (s + 3) 0), ?_, ?_⟩
  · change ((t.val : Mat K (s + 3)) * (g0.val : Mat K (s + 3))) *ᵥ v = _
    rw [← Matrix.mulVec_mulVec, hg0]
    exact ht0
  · change ((t.val : Mat K (s + 3)) * (g0.val : Mat K (s + 3))) *ᵥ w = _
    rw [← Matrix.mulVec_mulVec]
    exact htw

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBVectorCoordinates
