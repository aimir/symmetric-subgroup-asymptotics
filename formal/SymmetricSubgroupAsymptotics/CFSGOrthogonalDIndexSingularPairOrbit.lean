import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTailSingularOrbit
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexSingularRootPlanes

/-! Original D root words normalize an independent mutually polar-
orthogonal Q-singular pair in every characteristic. No full orthogonal
group equality or assumed transitivity is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexVectorCoordinates
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexTailCoordinates
open CFSGOrthogonalDIndexQuadraticForm CFSGOrthogonalDIndexAllRankQuadraticForm
open CFSGOrthogonalDIndexPolarForm CFSGOrthogonalDIndexFlagVectors
variable (K : Type) [Field K]

theorem exists_singular_pair_frame (s : ℕ)
    (v w : Index (s + 4) → K) (hv : v ≠ 0)
    (hsv : splitQ K v = 0) (hsw : splitQ K w = 0)
    (hvw : polar K v w = 0) (hnot : ∀ c : K, w ≠ c • v) :
    ∃ g : elementaryRootGroup K (s + 4), ∃ c : K,
      (g.val : Mat K (s + 4)) *ᵥ v = Pi.single (Sum.inl 0) 1 ∧
      (g.val : Mat K (s + 4)) *ᵥ w = c • Pi.single (Sum.inl 0) 1 +
        Pi.single (Sum.inl (secondIndex s)) 1 := by
  obtain ⟨g0, hg0⟩ := exists_normalize_singular K (s + 2) v hv hsv
  let w0 := (g0.val : Mat K (s + 4)) *ᵥ w
  have hp : polar K (Pi.single (Sum.inl 0) 1) w0 = 0 := by
    rw [← hg0]
    exact (elementary_preserves_polar K s g0 v w).trans hvw
  have hn : w0 (Sum.inr 0) = 0 :=
    (pairing_first_positive K (s + 3) w0).symm.trans hp
  have hw0s : splitQ K w0 = 0 :=
    (elementary_preserves_splitQ_all_ranks K (s + 4) (by omega) g0 w).trans hsw
  have ht : tailRestriction K (s + 3) w0 ≠ 0 := by
    intro hz
    have he := vector_eq_first_of_tail_zero K (s + 3) w0 hz hn
    have hb := congrArg (fun x : Index (s + 4) → K => (↑(g0.val⁻¹) : Mat K (s + 4)) *ᵥ x) he
    change (↑(g0.val⁻¹) : Mat K (s + 4)) *ᵥ ((g0.val : Mat K (s + 4)) *ᵥ w) =
      (↑(g0.val⁻¹) : Mat K (s + 4)) *ᵥ
        (w0 (Sum.inl 0) • Pi.single (Sum.inl 0) 1) at hb
    rw [← hg0] at hb
    simp only [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at hb
    exact hnot _ hb
  obtain ⟨t, ht0, htw⟩ := exists_tail_normalize_singular K s w0 hn ht hw0s
  refine ⟨t * g0, w0 (Sum.inl 0), ?_, ?_⟩
  · change ((t.val : Mat K (s + 4)) * (g0.val : Mat K (s + 4))) *ᵥ v = _
    rw [← Matrix.mulVec_mulVec, hg0]
    exact ht0
  · change ((t.val : Mat K (s + 4)) * (g0.val : Mat K (s + 4))) *ᵥ w = _
    rw [← Matrix.mulVec_mulVec]
    exact htw

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexVectorCoordinates
