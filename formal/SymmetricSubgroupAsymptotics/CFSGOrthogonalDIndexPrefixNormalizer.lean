import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPrefixFixedSpace

/-! Normalizers of the actual D flag-unipotent subgroup preserve all
positive prefixes of dimension at most r-1. No claim separates the
remaining hyperbolic pair, or asserts a Sylow or full Borel normalizer. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPrefixNormalizer
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexUnipotent
open CFSGOrthogonalDIndexPrefixFixedSpace CFSGMatrixFlagNormalizer
variable (K : Type) [Field K]

def naturalMatrixHom (r : ℕ) : elementaryRootGroup K r →* Mat K r :=
  (Units.coeHom (Mat K r)).comp (elementaryRootGroup K r).subtype

theorem normalizer_preserves_positivePrefix (s : ℕ)
    (A : elementaryRootGroup K (s + 4))
    (hA : A ∈ Subgroup.normalizer
      (unipotent K (s + 4) : Set (elementaryRootGroup K (s + 4)))) :
    ∀ k, k < s + 4 → ∀ v : Index (s + 4) → K,
      v ∈ flagPrefix (K := K) (flagEquiv (s + 4)) k →
      (A.val : Mat K (s + 4)) *ᵥ v ∈
        flagPrefix (K := K) (flagEquiv (s + 4)) k := by
  intro k
  induction k with
  | zero =>
    intro _ v hv
    have hz : v = 0 := funext fun i => hv i (Nat.zero_le _)
    rw [hz, Matrix.mulVec_zero]
    exact (flagPrefix (K := K) (flagEquiv (s + 4)) 0).zero_mem
  | succ k ih =>
    intro hk v hv
    apply prefix_succ_of_fixed K s k hk _
    intro u
    let c : elementaryRootGroup K (s + 4) := A⁻¹ * u.val * A
    have hc : c ∈ unipotent K (s + 4) :=
      (Subgroup.mem_normalizer_iff''.mp hA u.val).mp u.property
    have hm := prefix_succ_fixed K s k v hv ⟨c, hc⟩
    have h := ih (by omega) _ hm
    have he : A * c = u.val * A := by
      dsimp only [c]
      simp only [← mul_assoc, mul_inv_cancel, one_mul]
    have hM := congrArg (naturalMatrixHom K (s + 4)) he
    rw [map_mul, map_mul] at hM
    change (A.val : Mat K (s + 4)) * (c.val : Mat K (s + 4)) =
      (u.val.val : Mat K (s + 4)) * (A.val : Mat K (s + 4)) at hM
    have hact : (A.val : Mat K (s + 4)) *ᵥ ((c.val : Mat K (s + 4)) *ᵥ v) =
        (u.val.val : Mat K (s + 4)) *ᵥ ((A.val : Mat K (s + 4)) *ᵥ v) := by
      rw [Matrix.mulVec_mulVec, hM, ← Matrix.mulVec_mulVec]
    change (A.val : Mat K (s + 4)) *ᵥ ((c.val : Mat K (s + 4)) *ᵥ v - v) ∈
      flagPrefix (K := K) (flagEquiv (s + 4)) k at h
    simpa only [Matrix.mulVec_sub, hact] using h

theorem normalizer_positive_column_zero (s : ℕ)
    (A : elementaryRootGroup K (s + 4))
    (hA : A ∈ Subgroup.normalizer
      (unipotent K (s + 4) : Set (elementaryRootGroup K (s + 4))))
    (j : Fin (s + 4)) (hj : j.val + 1 < s + 4)
    (i : Index (s + 4)) (hi : j.val < (flagEquiv (s + 4) i).val) :
    (A.val : Mat K (s + 4)) i (Sum.inl j) = 0 := by
  have hv : Pi.single (Sum.inl j) (1 : K) ∈
      flagPrefix (K := K) (flagEquiv (s + 4)) (j.val + 1) := by
    intro x hx
    have hne : x ≠ Sum.inl j := by
      intro he
      subst x
      change j.val + 1 ≤ j.val at hx
      omega
    exact Pi.single_eq_of_ne hne 1
  have h := normalizer_preserves_positivePrefix K s A hA (j.val + 1) hj _ hv i
    (by omega)
  change ((A.val : Mat K (s + 4)) *ᵥ Pi.single (Sum.inl j) 1) i = 0 at h
  rw [Matrix.mulVec_single_one] at h
  exact h

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPrefixNormalizer
