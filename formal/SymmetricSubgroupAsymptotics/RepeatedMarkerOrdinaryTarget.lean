import SymmetricSubgroupAsymptotics.RepeatedMarkerFixedProfileBound
import SymmetricSubgroupAsymptotics.OrdinaryRemainderAssembly

/-!
# Complete ordinary targets for the positive-defect marker row

The actual merged physical family injects, after an original point
relabeling, into all subgroups on its degree. Thus the fixed-profile
presentation bound gives a forward row in complete ordinary subgroup
counts, without a boundedness input. Every coefficient keeps the original
marker denominator and the complete pair occurrence-factorial ratio.

The numerical positive-defect contraction is separate. In particular,
this unrestricted target must not replace the zero-defect remainder
target. Strict decrease is recorded for profiles with a positive number
of original markers; pure fixed-point removal is a separate operation.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.RepeatedMarkerOrdinaryTarget

open RepeatedMarkerMergedProfile RepeatedMarkerFixedProfileBound

variable {α : Type} [Fintype α] (Ω : α → Type)
    [∀ a, Fintype (Ω a)] [∀ a, Nonempty (Ω a)]
    (m : α → ℕ) (U : ∀ a, Subgroup (Equiv.Perm (Ω a)))

def sourceDegree (p g : ℕ) : ℕ := 3*g + (2*p + exteriorDegree Ω m)
def targetDegree (p q : ℕ) : ℕ := 2*(q+p) + exteriorDegree Ω m

/-- Every original presentation cost is retained. -/
def coefficient (p g q : ℕ) : ℚ :=
  ((sourceDegree Ω m p g).factorial : ℚ) / (targetDegree Ω m p q).factorial *
    ((2 : ℚ)^q * RepeatedMarkerAllocationWeights.markerProfileSum (Q := Fin q) g /
      (6 : ℚ)^g) * (((q+p).factorial : ℚ) / p.factorial)

theorem markerProfileSum_nonneg (g q : ℕ) :
    (0 : ℚ) ≤ RepeatedMarkerAllocationWeights.markerProfileSum (Q := Fin q) g := by
  unfold RepeatedMarkerAllocationWeights.markerProfileSum
    RepeatedMarkerAllocationWeights.profileSum
  apply Finset.sum_nonneg
  intro a _
  apply Finset.prod_nonneg
  intro i _
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem coefficient_nonneg (p g q : ℕ) : 0 ≤ coefficient Ω m p g q := by
  unfold coefficient
  exact mul_nonneg
    (mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (div_nonneg (mul_nonneg (by positivity) (markerProfileSum_nonneg g q))
        (by positivity)))
    (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

/-- The map forgets only the merged-profile property. The original
permutation subgroup is transported by an actual bijection of points. -/
theorem collapsed_card_le_subgroupCount (p q : ℕ) :
    Nat.card (CollapsedFamily Ω m U p q) ≤ subgroupCount (targetDegree Ω m p q) := by
  let e : ModelPoints Ω m (q+p) ≃ Fin (targetDegree Ω m p q) :=
    orbitProfileFinLabels (points Ω) (RepeatedMarkerMergedProfile.multiplicity m (q+p))
      (targetDegree Ω m p q) (degree Ω m (q+p))
  change _ ≤ Nat.card (Subgroup (Equiv.Perm (Fin (targetDegree Ω m p q))))
  exact Nat.card_le_card_of_injective
    (fun H : CollapsedFamily Ω m U p q => relabelSubgroup e H.1)
    (fun _ _ h => Subtype.ext ((relabelSubgroup e).injective h))

/-- A positive number of original markers guarantees strict decrease
for every retained width, including the empty-width contribution. -/
theorem target_lt_source (p g q : ℕ) (hg : 0 < g) (hq : q ≤ g) :
    targetDegree Ω m p q < sourceDegree Ω m p g := by
  unfold targetDegree sourceDegree
  omega

theorem target_width_lt_source (p g : ℕ) (hg : 0 < g)
    (q : RepeatedMarkerPresentationSum.Width (ι := Fin g)) :
    targetDegree Ω m p q.1 < sourceDegree Ω m p g := by
  apply target_lt_source Ω m p g q.1 hg
  have hq := q.2
  change q.1 < Fintype.card (Fin g) + 1 at hq
  simp only [Fintype.card_fin] at hq
  omega

/-- The complete original physical profile, with any earlier ownership
predicate retained on its literal subgroup, has an ordinary-target row. -/
theorem card_restricted_le (p g : ℕ) {X : Type}
    (chart : RepeatedOddMarkerPhysicalProfile.ModelPoints (points Ω) (RepeatedMarkerMergedProfile.multiplicity m p) g ≃ X)
    (hU : ∀ a, IsPGroup 2 (U a))
    (htrans : ∀ a (x y : Ω a), ∃ u : U a, (u : Equiv.Perm (Ω a)) x = y)
    (hsep : OrbitActionTypesSeparated Ω U)
    (hdegree : ∀ a, Fintype.card (Ω a) ≠ 2)
    (P : Subgroup (Equiv.Perm X) → Prop) :
    (Nat.card {H : OriginalFamily Ω m U p g X // P H.1} : ℚ) ≤
      ∑ q : RepeatedMarkerPresentationSum.Width (ι := Fin g),
        coefficient Ω m p g q.1 * (subgroupCount (targetDegree Ω m p q.1) : ℚ) := by
  apply (card_restricted_physical_le Ω m U p g chart hU htrans hsep hdegree P).trans
  apply Finset.sum_le_sum
  intro q _
  exact mul_le_mul_of_nonneg_left
    (by exact_mod_cast collapsed_card_le_subgroupCount Ω m U p q.1)
    (coefficient_nonneg Ω m p g q.1)

/-- Benchmark normalization changes no physical source weight. -/
def normalizedCoefficient (p g q : ℕ) : ℝ :=
  (coefficient Ω m p g q : ℝ) * exactBenchmark (targetDegree Ω m p q) /
    exactBenchmark (sourceDegree Ω m p g)

theorem normalizedCoefficient_nonneg (p g q : ℕ) :
    0 ≤ normalizedCoefficient Ω m p g q := by
  unfold normalizedCoefficient
  exact div_nonneg
    (mul_nonneg (by exact_mod_cast coefficient_nonneg Ω m p g q)
      (exactBenchmark_pos _).le) (exactBenchmark_pos _).le

/-- This is a finite row against complete ordinary ratios. It is not an
assumption that those ratios are bounded, and it asserts no row decay. -/
theorem card_restricted_div_benchmark_le (p g : ℕ) {X : Type}
    (chart : RepeatedOddMarkerPhysicalProfile.ModelPoints (points Ω) (RepeatedMarkerMergedProfile.multiplicity m p) g ≃ X)
    (hU : ∀ a, IsPGroup 2 (U a))
    (htrans : ∀ a (x y : Ω a), ∃ u : U a, (u : Equiv.Perm (Ω a)) x = y)
    (hsep : OrbitActionTypesSeparated Ω U)
    (hdegree : ∀ a, Fintype.card (Ω a) ≠ 2)
    (P : Subgroup (Equiv.Perm X) → Prop) :
    (Nat.card {H : OriginalFamily Ω m U p g X // P H.1} : ℝ) /
        exactBenchmark (sourceDegree Ω m p g) ≤
      ∑ q : RepeatedMarkerPresentationSum.Width (ι := Fin g),
        normalizedCoefficient Ω m p g q.1 *
          ordinarySubgroupRatio (targetDegree Ω m p q.1) := by
  have hreal : (Nat.card {H : OriginalFamily Ω m U p g X // P H.1} : ℝ) ≤
      ∑ q : RepeatedMarkerPresentationSum.Width (ι := Fin g),
        (coefficient Ω m p g q.1 : ℝ) *
          (subgroupCount (targetDegree Ω m p q.1) : ℝ) := by
    exact_mod_cast card_restricted_le Ω m U p g chart hU htrans hsep hdegree P
  apply (div_le_div_of_nonneg_right hreal (exactBenchmark_pos _).le).trans_eq
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro q _
  unfold normalizedCoefficient ordinarySubgroupRatio
  field_simp [ne_of_gt (exactBenchmark_pos (targetDegree Ω m p q.1)),
    ne_of_gt (exactBenchmark_pos (sourceDegree Ω m p g))] <;> ring

end SymmetricSubgroupAsymptotics.RepeatedMarkerOrdinaryTarget

end
