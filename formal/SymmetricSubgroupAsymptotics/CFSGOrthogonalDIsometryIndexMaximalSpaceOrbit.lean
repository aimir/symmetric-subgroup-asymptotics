import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIsometryIndexRankTwoSpaces
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIsometryIndexSingularTail
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTailVectorAction
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexSingularVectorOrbit
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexAllRankQuadraticForm

/-! Actual elementary words carry every maximal singular space to the
positive space OR a literal one-pair-crossed space. This is not the false
claim that all maximal singular spaces lie in one elementary orbit.
Every subspace is singular for the original Q, including in characteristic
two, and every tail lift is an actual original root-group homomorphism. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIsometryIndexMaximalSpaceOrbit
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexPositiveSpace
open CFSGOrthogonalDIndexBundledQuadratic CFSGOrthogonalDIndexQuadraticForm
open CFSGOrthogonalDIndexQuadraticSubspacePoints CFSGOrthogonalDIndexTailCoordinates
open CFSGOrthogonalDIndexAllRankQuadraticForm CFSGOrthogonalDIndexVectorCoordinates
open CFSGOrthogonalDIsometryIndexSingularTail CFSGOrthogonalDIsometryIndexCrossingSpaces
open CFSGOrthogonalDIsometryIndexRankTwoSpaces
variable (K : Type) [Field K]

def naturalSubspace (r : ℕ) (hr : 2 ≤ r) (g : elementaryRootGroup K r)
    (P : Subspaces (splitQuadraticForm K r)) : Subspaces (splitQuadraticForm K r) :=
  ⟨P.val.map (naturalLinearHom K r g).toLinearMap, by
    rintro x ⟨y, hy, rfl⟩
    rw [splitQuadraticForm_apply]
    exact (elementary_preserves_splitQ_all_ranks K r hr g y).trans
      ((splitQuadraticForm_apply K r y).symm.trans (P.property y hy))⟩

theorem naturalSubspace_finrank (r : ℕ) (hr : 2 ≤ r) (g : elementaryRootGroup K r)
    (P : Subspaces (splitQuadraticForm K r)) :
    Module.finrank K (naturalSubspace K r hr g P).val = Module.finrank K P.val :=
  (naturalLinearHom K r g).finrank_map_eq P.val

theorem exists_normalize_singular_of_two_le (r : ℕ) (hr : 2 ≤ r)
    (v : Index r → K) (hv : v ≠ 0) (hz : splitQuadraticForm K r v = 0) :
    ∃ g : elementaryRootGroup K r,
      (g.val : Mat K r) *ᵥ v = Pi.single (Sum.inl (⟨0, by omega⟩ : Fin r)) 1 := by
  obtain ⟨s, rfl⟩ : ∃ s : ℕ, r = s + 2 := ⟨r - 2, by omega⟩
  exact exists_normalize_singular K s v hv
    ((splitQuadraticForm_apply K (s + 2) v).symm.trans hz)

theorem exists_normalize_full_rank (r : ℕ) (hr : 2 ≤ r) :
    ∀ (P : Subspaces (splitQuadraticForm K r)), Module.finrank K P.val = r →
    ∃ g : elementaryRootGroup K r,
      P.val.map (naturalLinearHom K r g).toLinearMap = positiveSpace K r ∨
      ∃ j : Fin r, P.val.map (naturalLinearHom K r g).toLinearMap = crossingSpace K r j := by
  induction r, hr using Nat.le_induction with
  | base =>
    intro P hd
    exact exists_normalize_rank_two K P.val hd P.property
  | succ n hn ih =>
    intro P hd
    have hPne : P.val ≠ ⊥ := Submodule.one_le_finrank_iff.mp (by rw [hd]; omega)
    obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hPne
    obtain ⟨g, hg⟩ := exists_normalize_singular_of_two_le K (n + 1) (by omega) u hu0
      (P.property u hu)
    let P₀ := naturalSubspace K (n + 1) (by omega) g P
    have hP₀ : Module.finrank K P₀.val = n + 1 :=
      (naturalSubspace_finrank K (n + 1) (by omega) g P).trans hd
    have he₀ : Pi.single (Sum.inl (0 : Fin (n + 1))) 1 ∈ P₀.val := ⟨u, hu, hg⟩
    let T := tailSubspace K n P₀ he₀
    have hT : Module.finrank K T.val = n := by
      have ht := tailSubspace_finrank K n P₀ he₀
      change Module.finrank K T.val + 1 = Module.finrank K P₀.val at ht
      rw [hP₀] at ht
      omega
    obtain ⟨h, hh⟩ := ih T hT
    let t := tailElementaryHom K n hn h
    let P₁ := P₀.val.map (naturalLinearHom K (n + 1) t).toLinearMap
    have hP₁ : Module.finrank K P₁ = n + 1 :=
      ((naturalLinearHom K (n + 1) t).finrank_map_eq P₀.val).trans hP₀
    have hmap : P.val.map (naturalLinearHom K (n + 1) (t * g)).toLinearMap = P₁ := by
      change P.val.map (Matrix.mulVecLin ((t.val : Mat K (n + 1)) *
        (g.val : Mat K (n + 1)))) = _
      rw [Matrix.mulVecLin_mul, Submodule.map_comp]
      rfl
    have hnegative (x : Index (n + 1) → K) (hx : x ∈ P₀.val) :
        ((t.val : Mat K (n + 1)) *ᵥ x) (Sum.inr 0) = 0 := by
      rw [tailElementaryHom_head_negative]
      exact negative_head_zero K n P₀ he₀ x hx
    have htail (x : Index (n + 1) → K) (hx : x ∈ P₀.val) :
        tailRestrictionLinear K n ((t.val : Mat K (n + 1)) *ᵥ x) ∈
          T.val.map (naturalLinearHom K n h).toLinearMap := by
      change tailRestriction K n ((t.val : Mat K (n + 1)) *ᵥ x) ∈ _
      rw [tailElementaryHom_tail_action]
      exact ⟨tailRestriction K n x, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨t * g, ?_⟩
    rw [hmap]
    rcases hh with hpos | ⟨j, hcross⟩
    · left
      apply Submodule.eq_of_le_of_finrank_le
      · rintro v ⟨x, hx, rfl⟩
        apply positive_of_tail K n _ (hnegative x hx)
        have hm := htail x hx
        rwa [hpos] at hm
      · rw [positiveSpace_finrank, hP₁]
    · right
      refine ⟨j.succ, Submodule.eq_of_le_of_finrank_le ?_ ?_⟩
      · rintro v ⟨x, hx, rfl⟩
        apply crossing_of_tail K n j _ (hnegative x hx)
        have hm := htail x hx
        rwa [hcross] at hm
      · rw [crossingSpace_finrank, hP₁]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIsometryIndexMaximalSpaceOrbit
