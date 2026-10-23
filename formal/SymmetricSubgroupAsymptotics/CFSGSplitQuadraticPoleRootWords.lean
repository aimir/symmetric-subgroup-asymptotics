import SymmetricSubgroupAsymptotics.CFSGSplitQuadraticPoleChainAction
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexAllRankRootLines
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-! Every literal quadratic pole shear is an actual word in the split-D
root subgroup. The word fixes the positive pole and clears a normalized
singular companion, uniformly in every characteristic and rank at least two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGSplitQuadraticPoleRootWords
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexTailCoordinates
open CFSGOrthogonalDIndexQuadraticForm CFSGSplitQuadraticPoleCoordinates
open CFSGSplitQuadraticPoleRootAction CFSGSplitQuadraticPoleChainAction
open CFSGOrthogonalDIndexAllRankRootLines CFSGQuadraticHyperbolicShear
variable (K : Type) [Field K]

theorem single_has_element (n : ℕ) (hn : 0 < n) (i : Index n) (a : K) :
    ∃ g : elementaryRootGroup K (n + 1), ∀ v : Index (n + 1) → K,
      (g.val : Mat K (n + 1)) *ᵥ v = poleShear K n (Pi.single i a) v := by
  cases i with
  | inl j =>
    obtain ⟨u, hu, he⟩ := plus_line_all_ranks K (n + 1) (by omega) 0 j.succ
      (Ne.symm (Fin.succ_ne_zero j)) (-a)
    refine ⟨⟨u, hu⟩, ?_⟩
    intro v
    rw [positive_single_action]
    exact congrArg (fun M : Mat K (n + 1) => M *ᵥ v) he
  | inr j =>
    obtain ⟨u, hu, he⟩ := chain_line_all_ranks K (n + 1) 0 j.succ
      (Ne.symm (Fin.succ_ne_zero j)) (-a)
    refine ⟨⟨u, hu⟩, ?_⟩
    intro v
    rw [negative_single_action]
    exact congrArg (fun M : Mat K (n + 1) => M *ᵥ v) he

theorem poleShear_has_element (n : ℕ) (hn : 0 < n) (z : Index n → K) :
    ∃ g : elementaryRootGroup K (n + 1), ∀ v : Index (n + 1) → K,
      (g.val : Mat K (n + 1)) *ᵥ v = poleShear K n z v := by
  classical
  have hsum (t : Finset (Index n)) :
      ∃ g : elementaryRootGroup K (n + 1), ∀ v : Index (n + 1) → K,
        (g.val : Mat K (n + 1)) *ᵥ v =
          poleShear K n (∑ i ∈ t, Pi.single i (z i)) v := by
    induction t using Finset.induction_on with
    | empty =>
      refine ⟨1, ?_⟩
      intro v
      change (1 : Mat K (n + 1)) *ᵥ v = _
      simp only [Finset.sum_empty, poleShear_zero_apply, Matrix.one_mulVec]
    | @insert i t hi ih =>
      obtain ⟨a, ha⟩ := single_has_element K n hn i (z i)
      obtain ⟨b, hb⟩ := ih
      refine ⟨a * b, ?_⟩
      intro v
      change ((a.val : Mat K (n + 1)) * (b.val : Mat K (n + 1))) *ᵥ v = _
      rw [← Matrix.mulVec_mulVec, ha, hb, Finset.sum_insert hi, poleShear_add_apply]
  have hz : (∑ i : Index n, Pi.single i (z i)) = z := by
    funext i
    rw [Finset.sum_apply]
    exact Fintype.sum_pi_single i z
  obtain ⟨g, hg⟩ := hsum Finset.univ
  exact ⟨g, fun v => by simpa only [hz] using hg v⟩

theorem poleShear_fix_positive_axis (n : ℕ) (z : Index n → K) :
    poleShear K n z (Pi.single (Sum.inl 0) 1) = Pi.single (Sum.inl 0) 1 := by
  apply (coordinateEquiv K n).injective
  change coordinates K n (poleShear K n z (Pi.single (Sum.inl 0) 1)) =
    coordinates K n (Pi.single (Sum.inl 0) 1)
  rw [coordinates_poleShear]
  have he : coordinates K n (Pi.single (Sum.inl 0) 1) = (1, (0, 0)) := by
    apply Prod.ext
    · simp [coordinates]
    · apply Prod.ext
      · funext i
        cases i <;> simp [coordinates, tailIndex, Function.comp_apply]
      · simp [coordinates]
  rw [he]
  exact transform_fix_axis _ z

theorem exists_normalize_companion (n : ℕ) (hn : 0 < n) (v : Index (n + 1) → K)
    (hy : v (Sum.inr 0) = 1) (hQ : splitQ K v = 0) :
    ∃ g : elementaryRootGroup K (n + 1),
      (g.val : Mat K (n + 1)) *ᵥ Pi.single (Sum.inl 0) 1 = Pi.single (Sum.inl 0) 1 ∧
      (g.val : Mat K (n + 1)) *ᵥ v = Pi.single (Sum.inr 0) 1 := by
  obtain ⟨g, hg⟩ := poleShear_has_element K n hn (-(v ∘ tailIndex n))
  refine ⟨g, ?_, ?_⟩
  · rw [hg, poleShear_fix_positive_axis]
  · rw [hg]
    exact poleShear_normalize_companion K n v hy hQ

end SymmetricSubgroupAsymptotics.CFSGSplitQuadraticPoleRootWords
