import SymmetricSubgroupAsymptotics.RepeatedMarkerAggregateProfile
import SymmetricSubgroupAsymptotics.MarkerNormalizedKernel
import SymmetricSubgroupAsymptotics.RepeatedMarkerProfileSmall

/-!
# The actual profile coefficient equals the complete normalized marker kernel

The natural support balance constructs the actual MarkerGeometry parameter.
Zero selected width with positive marker count contributes exactly zero,
by the complete multiplicity-sum identity. The final theorem concerns the
actual fixed-support family; its exterior profiles have already been
summed without multiplicity loss. It makes no boundedness assumption on
the complete ordinary subgroup ratios.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.RepeatedMarkerNormalizedProfile

open MarkerGeometry MarkerNormalizedKernel RepeatedMarkerAggregateProfile

abbrev Width (g : ℕ) := RepeatedMarkerPresentationSum.Width (ι := Fin g)
abbrev AdmissibleWidth (g : ℕ) := {q : Width g // g = 0 ∨ 1 ≤ q.1}

theorem width_le (g : ℕ) (q : Width g) : q.1 ≤ g := by
  have h := q.2
  change q.1 < Fintype.card (Fin g) + 1 at h
  simp only [Fintype.card_fin] at h
  omega

/-- The actual support identities provide every admissibility field. -/
def parameter (N epsilon r g f : ℕ) (hepsilon : epsilon ≤ 1)
    (hn : totalDegree r g f = 2*N+epsilon) (q : AdmissibleWidth g) :
    Parameters N epsilon where
  M := r+q.1.1
  g := g
  f := f
  q := q.1.1
  parity := hepsilon
  balance := by unfold totalDegree at hn; omega
  q_le_g := width_le g q.1
  q_le_M := by omega
  positive_signs := q.2

theorem parameter_defect (N epsilon r g f : ℕ) (hepsilon : epsilon ≤ 1)
    (hn : totalDegree r g f = 2*N+epsilon) (q : AdmissibleWidth g) :
    (parameter N epsilon r g f hepsilon hn q).defect = (g+f-epsilon)/2 := rfl

theorem coefficient_cast (r g f q : ℕ) :
    (RepeatedMarkerAggregateProfile.coefficient r g f q : ℝ) =
      (((totalDegree r g f).factorial : ℝ) / (targetDegree r q).factorial) *
        (markerWeight g f q *
          (RepeatedMarkerAllocationWeights.markerProfileSum (Q := Fin q) g : ℝ)) *
        ((r+q).descFactorial q : ℝ) := by
  unfold RepeatedMarkerAggregateProfile.coefficient markerWeight
  push_cast
  ring

theorem coefficient_eq_zero_of_not_admissible (r g f : ℕ) (q : Width g)
    (hq : ¬ (g = 0 ∨ 1 ≤ q.1)) :
    RepeatedMarkerAggregateProfile.coefficient r g f q.1 = 0 := by
  have hg : g ≠ 0 := fun hg => hq (Or.inl hg)
  have hzero : q.1 = 0 := by omega
  unfold RepeatedMarkerAggregateProfile.coefficient
  rw [hzero,RepeatedMarkerProfileSmall.markerProfileSum_fin_zero_of_ne g hg]
  simp

/-- Exact cancellation of original factorials against the actual guarded
benchmark, with no replacement of the odd coefficient by the even one. -/
theorem normalized_coefficient_eq (N epsilon r g f : ℕ) (hepsilon : epsilon ≤ 1)
    (hn : totalDegree r g f = 2*N+epsilon) (q : AdmissibleWidth g) :
    (RepeatedMarkerAggregateProfile.coefficient r g f q.1.1 : ℝ) *
        exactBenchmark (targetDegree r q.1.1) / exactBenchmark (2*N+epsilon) =
      profileKernel (parameter N epsilon r g f hepsilon hn q) := by
  rw [coefficient_cast,hn]
  change (((( (2*N+epsilon).factorial : ℝ) / (2*(r+q.1.1)).factorial) *
      (markerWeight g f q.1.1 *
        (RepeatedMarkerAllocationWeights.markerProfileSum (Q := Fin q.1.1) g : ℝ)) *
      ((r+q.1.1).descFactorial q.1.1 : ℝ)) * exactBenchmark (2*(r+q.1.1)) /
        exactBenchmark (2*N+epsilon)) = _
  calc
    _ = ((((2*N+epsilon).factorial : ℝ) / (2*(r+q.1.1)).factorial) *
        exactBenchmark (2*(r+q.1.1)) / exactBenchmark (2*N+epsilon)) *
        (markerWeight g f q.1.1 *
          (RepeatedMarkerAllocationWeights.markerProfileSum (Q := Fin q.1.1) g : ℝ)) *
        ((r+q.1.1).descFactorial q.1.1 : ℝ) := by ring
    _ = _ := by
      rw [factorial_benchmark_ratio N epsilon (r+q.1.1) hepsilon]
      rfl

variable {α : Type} [Fintype α] (Ω : α → Type)
    [∀ a, Fintype (Ω a)] [∀ a, Nonempty (Ω a)]
    (U : ∀ a, Subgroup (Equiv.Perm (Ω a)))

/-- The fixed original support family receives its actual normalized
parameter row. No per-profile or total subgroup count is supplied. -/
theorem card_family_div_benchmark_le (N epsilon r g f : ℕ) (hepsilon : epsilon ≤ 1)
    (hn : totalDegree r g f = 2*N+epsilon)
    (S : Finset (Profile (α := α)))
    (hsize : ∀ t ∈ S, 2*t.1 + RepeatedMarkerMergedProfile.exteriorDegree Ω t.2 = 2*r)
    (hU : ∀ a, IsPGroup 2 (U a))
    (htrans : ∀ a (x y : Ω a), ∃ u : U a, (u : Equiv.Perm (Ω a)) x = y)
    (hsep : OrbitActionTypesSeparated Ω U)
    (hdegreeOne : ∀ a, Fintype.card (Ω a) ≠ 1)
    (hdegreeTwo : ∀ a, Fintype.card (Ω a) ≠ 2)
    (P : Subgroup (Equiv.Perm (Fin (totalDegree r g f))) → Prop) :
    (Nat.card (Family Ω U r g f S P) : ℝ) / exactBenchmark (2*N+epsilon) ≤
      ∑ q : AdmissibleWidth g,
        profileKernel (parameter N epsilon r g f hepsilon hn q) *
          ordinarySubgroupRatio (2*(r+q.1.1)) := by
  have hc : (Nat.card (Family Ω U r g f S P) : ℝ) ≤
      ∑ q : Width g, (RepeatedMarkerAggregateProfile.coefficient r g f q.1 : ℝ) *
        (subgroupCount (targetDegree r q.1) : ℝ) := by
    exact_mod_cast RepeatedMarkerAggregateProfile.card_family_le Ω U r g f S hsize
      hU htrans hsep hdegreeOne hdegreeTwo P
  apply (div_le_div_of_nonneg_right hc (exactBenchmark_pos _).le).trans_eq
  rw [Finset.sum_div]
  let w : Width g → ℝ := fun q =>
    (RepeatedMarkerAggregateProfile.coefficient r g f q.1 : ℝ) *
      (subgroupCount (targetDegree r q.1) : ℝ) / exactBenchmark (2*N+epsilon)
  have hbad : (∑ q : {q : Width g // ¬ (g = 0 ∨ 1 ≤ q.1)}, w q.1) = 0 := by
    apply Finset.sum_eq_zero
    intro q _
    dsimp only [w]
    rw [coefficient_eq_zero_of_not_admissible r g f q.1 q.2]
    simp
  have hsplit := Fintype.sum_subtype_add_sum_subtype
    (fun q : Width g => g = 0 ∨ 1 ≤ q.1) w
  rw [hbad,add_zero] at hsplit
  change (∑ q : Width g, w q) = _
  rw [← hsplit]
  apply Finset.sum_congr rfl
  intro q _
  dsimp only [w]
  rw [← normalized_coefficient_eq N epsilon r g f hepsilon hn q]
  unfold ordinarySubgroupRatio
  change _ =
    ((RepeatedMarkerAggregateProfile.coefficient r g f q.1.1 : ℝ) *
      exactBenchmark (targetDegree r q.1.1) / exactBenchmark (2*N+epsilon)) *
      ((subgroupCount (targetDegree r q.1.1) : ℝ) / exactBenchmark (targetDegree r q.1.1))
  field_simp [ne_of_gt (exactBenchmark_pos (targetDegree r q.1.1)),
    ne_of_gt (exactBenchmark_pos (2*N+epsilon))] <;> ring

end SymmetricSubgroupAsymptotics.RepeatedMarkerNormalizedProfile

end
