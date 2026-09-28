import SymmetricSubgroupAsymptotics.GrowingQuotientForwardEstimate
import SymmetricSubgroupAsymptotics.FusionPhysicalUnion
import SymmetricSubgroupAsymptotics.FusionWidthPhysical

/-!
# Assembly of literal growing quotient families

This file discharges the finite-union algebra between local whole-axis
quotient bounds and `GrowingQuotientPhysicalBound`.  Widths, action labels,
the full physical predicate, and the original action divisor remain indexed
literally throughout the assembly.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

variable {ι : ℕ → Type*} [∀ w, Fintype (ι w)]

private theorem sum_Ico_subtype {w₀ n : ℕ} (f : ℕ → ℝ) :
    (∑ w : {w : ℕ // w ∈ Finset.Ico w₀ (n + 1)}, f w.1) =
      ∑ w ∈ Finset.Ico w₀ (n + 1), f w := by
  exact (Finset.sum_subtype (Finset.Ico w₀ (n + 1))
    (fun _ => Iff.rfl) f).symm

abbrev GrowingQuotientPhysicalIndex (w₀ n : ℕ) :=
  Σ w : {w : ℕ // w ∈ Finset.Ico w₀ (n + 1)}, ι w.1

def growingQuotientPhysicalWidth {w₀ n : ℕ}
    (j : GrowingQuotientPhysicalIndex (ι := ι) w₀ n) : ℕ :=
  j.1.1

theorem growingQuotientPhysicalWidth_le {w₀ n : ℕ}
    (j : GrowingQuotientPhysicalIndex (ι := ι) w₀ n) :
    growingQuotientPhysicalWidth j ≤ n := by
  unfold growingQuotientPhysicalWidth
  exact Nat.lt_succ_iff.mp (Finset.mem_Ico.mp j.1.2).2

def GrowingQuotientCanonicalFamily
    (w₀ n : ℕ)
    (U : ∀ w, ι w → Subgroup (Equiv.Perm (Fin w)))
    (P : ∀ w (i : ι w) b,
      Subgroup (U w i × Equiv.Perm (Fin b)) → Prop)
    (j : GrowingQuotientPhysicalIndex (ι := ι) w₀ n) :
    Set (Subgroup (Equiv.Perm (Fin n))) :=
  FusionWidthCanonicalFamily (U j.1.1 j.2)
    (growingQuotientPhysicalWidth_le j) (P j.1.1 j.2 (n-j.1.1))

/-- Exact local inequality required from the complete-source comparator
certificate for every retained width and action. -/
def GrowingQuotientLocalPhysicalBound
    (w₀ : ℕ)
    (U : ∀ w, ι w → Subgroup (Equiv.Perm (Fin w)))
    (P : ∀ w (i : ι w) b,
      Subgroup (U w i × Equiv.Perm (Fin b)) → Prop)
    (D : ∀ w, ι w → ℕ → ℝ) (A : ∀ w, ι w → ℝ)
    (v : ∀ w, ι w → ℕ) (η δ c α : ∀ w, ι w → ℝ) : Prop :=
  ∀ n (j : GrowingQuotientPhysicalIndex (ι := ι) w₀ n),
    (Nat.card (GrowingQuotientCanonicalFamily w₀ n U P j) : ℝ) /
        exactBenchmark n ≤
      growingQuotientHotKernel (fun m => (subgroupCount m : ℝ))
          (n-j.1.1) j.1.1 (v j.1.1 j.2)
          (D j.1.1 j.2 (n-j.1.1)) (A j.1.1 j.2)
          (η j.1.1 j.2) (δ j.1.1 j.2) (c j.1.1 j.2) +
        fusionWidthColdKernel (n-j.1.1) j.1.1
          (D j.1.1 j.2 (n-j.1.1)) (A j.1.1 j.2)
          (α j.1.1 j.2) * ordinarySubgroupRatio (n-j.1.1)

/-- A uniform family of complete-source comparator envelopes supplies every
local physical inequality with the actual normalizer and the exact cold
slope. -/
theorem growingQuotientLocalPhysicalBound_of_completeSource
    (w₀ : ℕ)
    (U : ∀ w, ι w → Subgroup (Equiv.Perm (Fin w)))
    (P : ∀ w (i : ι w) b,
      Subgroup (U w i × Equiv.Perm (Fin b)) → Prop)
    (R : ∀ w, ι w → Type*)
    [∀ w i, Group (R w i)] [∀ w i, Finite (R w i)]
    (D : ∀ w, ι w → ℕ → ℝ) (A : ∀ w, ι w → ℝ)
    (v : ∀ w, ι w → ℕ) (η δ c α : ∀ w, ι w → ℝ)
    (ρR : ∀ w i, R w i →* Equiv.Perm (Fin (v w i)))
    (hρR : ∀ w i, Function.Injective (ρR w i))
    (hP : ∀ w i b, FusionOrbitNatural (U w i) (P w i b))
    (hD : ∀ w i b, 0 ≤ D w i b)
    (hA : ∀ w i, A w i =
      (Nat.card (Subgroup.normalizer
        (U w i : Set (Equiv.Perm (Fin w)))) : ℝ))
    (hα : ∀ w i, α w i = η w i + c w i)
    (henvelope : ∀ w i b (J : Subgroup (Equiv.Perm (Fin b))),
      fusionCompleteSourceSum (U w i) (P w i b) J ≤
        (D w i b * (2 : ℝ) ^ (η w i * b)) *
          completeQuotientWeight (R := R w i) J) :
    GrowingQuotientLocalPhysicalBound w₀ U P D A v η δ c α := by
  intro n j
  let w : ℕ := j.1.1
  let i : ι w := j.2
  have hwn : w ≤ n := growingQuotientPhysicalWidth_le j
  have hbound := fusionPhysical_growingQuotient_kernel_bound
    (U w i) (P w i (n-w)) (hP w i (n-w))
    (ρR w i) (hρR w i) (D w i (n-w))
      (η w i) (δ w i) (c w i) (hD w i (n-w))
      (henvelope w i (n-w))
  rw [GrowingQuotientCanonicalFamily, fusionWidthCanonicalFamily_card]
  simpa only [w, i, Nat.sub_add_cancel hwn, ordinarySubgroupRatio,
    hA w i, hα w i] using hbound

/-- A literal cover and the local complete-source estimates assemble into
the exact physical premise consumed by the uniform numerical theorem. -/
theorem growingQuotientPhysicalBound_of_local
    (error : ℕ → ℝ) (w₀ : ℕ) (hw₀ : 1 ≤ w₀)
    (F : ∀ n, Set (Subgroup (Equiv.Perm (Fin n))))
    (U : ∀ w, ι w → Subgroup (Equiv.Perm (Fin w)))
    (P : ∀ w (i : ι w) b,
      Subgroup (U w i × Equiv.Perm (Fin b)) → Prop)
    (D : ∀ w, ι w → ℕ → ℝ) (A : ∀ w, ι w → ℝ)
    (v : ∀ w, ι w → ℕ) (η δ c α : ∀ w, ι w → ℝ)
    (herror : ∀ᶠ n : ℕ in atTop,
      error n ≤ (Nat.card (F n) : ℝ) / exactBenchmark n)
    (hcover : ∀ n H, H ∈ F n →
      ∃ j : GrowingQuotientPhysicalIndex (ι := ι) w₀ n,
        H ∈ GrowingQuotientCanonicalFamily w₀ n U P j)
    (hlocal : GrowingQuotientLocalPhysicalBound w₀ U P D A v η δ c α) :
    GrowingQuotientPhysicalBound error w₀ D A v η δ c α := by
  filter_upwards [herror] with n herrorn
  have hcard := fusionPhysicalUnion_card_le (F n)
    (fun j : GrowingQuotientPhysicalIndex (ι := ι) w₀ n =>
      GrowingQuotientCanonicalFamily w₀ n U P j) (hcover n)
  have hcardR : (Nat.card (F n) : ℝ) ≤
      ∑ j : GrowingQuotientPhysicalIndex (ι := ι) w₀ n,
        (Nat.card (GrowingQuotientCanonicalFamily w₀ n U P j) : ℝ) := by
    exact_mod_cast hcard
  apply herrorn.trans
  calc
    (Nat.card (F n) : ℝ) / exactBenchmark n ≤
        (∑ j : GrowingQuotientPhysicalIndex (ι := ι) w₀ n,
          (Nat.card (GrowingQuotientCanonicalFamily w₀ n U P j) : ℝ)) /
            exactBenchmark n :=
      div_le_div_of_nonneg_right hcardR (exactBenchmark_pos n).le
    _ = ∑ j : GrowingQuotientPhysicalIndex (ι := ι) w₀ n,
        (Nat.card (GrowingQuotientCanonicalFamily w₀ n U P j) : ℝ) /
          exactBenchmark n := Finset.sum_div _ _ _
    _ ≤ ∑ j : GrowingQuotientPhysicalIndex (ι := ι) w₀ n,
        (growingQuotientHotKernel (fun m => (subgroupCount m : ℝ))
            (n-j.1.1) j.1.1 (v j.1.1 j.2)
            (D j.1.1 j.2 (n-j.1.1)) (A j.1.1 j.2)
            (η j.1.1 j.2) (δ j.1.1 j.2) (c j.1.1 j.2) +
          fusionWidthColdKernel (n-j.1.1) j.1.1
            (D j.1.1 j.2 (n-j.1.1)) (A j.1.1 j.2)
            (α j.1.1 j.2) * ordinarySubgroupRatio (n-j.1.1)) :=
      Finset.sum_le_sum (fun j _ => hlocal n j)
    _ = growingQuotientHotTotal (fun m => (subgroupCount m : ℝ))
          w₀ n D A v η δ c +
        ∑ b ∈ Finset.range n,
          growingQuotientColdRow w₀ D A α n b * ordinarySubgroupRatio b := by
      rw [Finset.sum_add_distrib, Fintype.sum_sigma, Fintype.sum_sigma]
      rw [growingQuotientColdRow_weighted_sum w₀ hw₀
        D A α ordinarySubgroupRatio n]
      let hot : ℕ → ℝ := fun w => ∑ i,
        growingQuotientHotKernel (fun m => (subgroupCount m : ℝ))
          (n-w) w (v w i) (D w i (n-w)) (A w i)
          (η w i) (δ w i) (c w i)
      let cold : ℕ → ℝ := fun w => (∑ i,
        fusionWidthColdKernel (n-w) w (D w i (n-w))
          (A w i) (α w i)) * ordinarySubgroupRatio (n-w)
      have hhot := sum_Ico_subtype (w₀ := w₀) (n := n) hot
      have hcold := sum_Ico_subtype (w₀ := w₀) (n := n) cold
      simpa only [hot, cold, growingQuotientHotTotal,
        growingQuotientColdWidthSum, Finset.sum_mul] using
          congrArg₂ (· + ·) hhot hcold

end SymmetricSubgroupAsymptotics

end
