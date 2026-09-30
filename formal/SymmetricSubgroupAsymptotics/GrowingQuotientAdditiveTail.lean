import SymmetricSubgroupAsymptotics.GrowingQuotientPhysicalAssembly
import SymmetricSubgroupAsymptotics.ForwardEstimateAlgebra

/-!
# Additive cold tails in growing quotient envelopes

Several physical owner families have a sharp local estimate of the form

`sourceSum J ≤ D · 2^(ηb) · Z_J(R) + T · 2^(θb)`.

The second term is independent of the complete source `J`.  It must not be
forced through the hot/cold threshold for `Z_J(R)`: after summing over `J` it
is already a pure cold row.  This file installs that row beside the usual
growing-comparator hot scalar and cold row, and proves one exponentially
contractive forward estimate when both weighted menu masses are
subquadratic.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

variable {ι : ℕ → Type*} [∀ w, Fintype (ι w)]

/-- Whole-axis quotient transfer with a source-independent additive tail.
The main term alone is split by the complete-quotient moment; the additive
term is summed over the literal complete sources and enters cold. -/
theorem fusionPhysical_completeQuotient_additiveTail_normalized_bound
    {R : Type*} [Group R] [Finite R] {w v b q : ℕ}
    (U : Subgroup (Equiv.Perm (Fin w)))
    (P : Subgroup (U × Equiv.Perm (Fin b)) → Prop)
    (hP : FusionOrbitNatural U P)
    (rhoR : R →* Equiv.Perm (Fin v)) (hrhoR : Function.Injective rhoR)
    (D T t : ℝ) (hD : 0 ≤ D) (hT : 0 ≤ T) (ht : 0 < t) (hq : 1 ≤ q)
    (henvelope : ∀ J,
      fusionCompleteSourceSum U P J ≤
        D * completeQuotientWeight (R := R) J + T) :
    (Nat.card
        (FusionOrbitFamily U (FusionAcceptedOrbitPredicate U P)) : ℝ) /
        exactBenchmark (b + w) ≤
      growingQuotientNormalizedPointing b w
          (Nat.card
            (Subgroup.normalizer
              (U : Set (Equiv.Perm (Fin w)))) : ℝ) *
        (D / t ^ (q - 1) * (subgroupCount (b + q * v) : ℝ) +
          (subgroupCount b : ℝ) * D * t +
          (subgroupCount b : ℝ) * T) := by
  let A : ℝ := Nat.card
    (Subgroup.normalizer (U : Set (Equiv.Perm (Fin w))))
  let point : ℝ := growingQuotientNormalizedPointing b w A
  have hA : 0 < A := by
    dsimp [A]
    exact_mod_cast (Nat.card_pos (α := Subgroup.normalizer
      (U : Set (Equiv.Perm (Fin w)))))
  have hpoint : 0 ≤ point := by
    dsimp [point]
    unfold growingQuotientNormalizedPointing
    exact div_nonneg
      (div_nonneg (div_nonneg (by positivity) (by positivity)) hA.le)
      (exactBenchmark_pos (b + w)).le
  have hmain := fusion_hot_cold_sum_le
    (fun J : Subgroup (Equiv.Perm (Fin b)) =>
      D * completeQuotientWeight (R := R) J)
    (completeQuotientWeight (R := R)) hD ht
    (completeQuotientWeight_nonneg (R := R))
    (fun J => le_rfl) hq
    (completeQuotientWeight_moment_le rhoR hrhoR b q)
  have hmain' :
      (∑ J : Subgroup (Equiv.Perm (Fin b)),
        D * completeQuotientWeight (R := R) J) ≤
        D / t ^ (q - 1) * (subgroupCount (b + q * v) : ℝ) +
          (subgroupCount b : ℝ) * D * t := by
    simpa only [subgroupCount] using hmain
  have hsum :
      (∑ J : Subgroup (Equiv.Perm (Fin b)),
          fusionCompleteSourceSum U P J) ≤
        (D / t ^ (q - 1) * (subgroupCount (b + q * v) : ℝ) +
          (subgroupCount b : ℝ) * D * t) +
          (subgroupCount b : ℝ) * T := by
    calc
      _ ≤ ∑ J : Subgroup (Equiv.Perm (Fin b)),
          (D * completeQuotientWeight (R := R) J + T) :=
        Finset.sum_le_sum (fun J _ => henvelope J)
      _ = (∑ J : Subgroup (Equiv.Perm (Fin b)),
          D * completeQuotientWeight (R := R) J) +
          (subgroupCount b : ℝ) * T := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          Fintype.card_eq_nat_card, subgroupCount]
      _ ≤ _ := by
        linarith
  have hphysical := fusionPhysical_original_weight U P hP
  simp only [Fintype.card_fin, Nat.add_comm w b] at hphysical
  have hnormalized :
      (Nat.card
          (FusionOrbitFamily U (FusionAcceptedOrbitPredicate U P)) : ℝ) /
          exactBenchmark (b + w) ≤
        point *
          (∑ J : Subgroup (Equiv.Perm (Fin b)),
            fusionCompleteSourceSum U P J) := by
    have hbench := exactBenchmark_pos (b + w)
    have hdiv := div_le_div_of_nonneg_right hphysical hbench.le
    convert hdiv using 1
    simp only [fusionCompleteSourceSum, Nat.cast_sum]
    rw [Finset.sum_comm]
    unfold fusionSurvivingEpiCount
    push_cast
    dsimp [point, growingQuotientNormalizedPointing, A]
    ring
  apply hnormalized.trans
  dsimp [A, point]
  exact mul_le_mul_of_nonneg_left (by linarith) hpoint

/-- Kernel form of the additive-tail transfer. -/
theorem fusionPhysical_growingQuotient_additiveTail_kernel_bound
    {R : Type*} [Group R] [Finite R] {w v b : ℕ}
    (U : Subgroup (Equiv.Perm (Fin w)))
    (P : Subgroup (U × Equiv.Perm (Fin b)) → Prop)
    (hP : FusionOrbitNatural U P)
    (rhoR : R →* Equiv.Perm (Fin v)) (hrhoR : Function.Injective rhoR)
    (D T eta theta delta c : ℝ) (hD : 0 ≤ D) (hT : 0 ≤ T)
    (henvelope : ∀ J,
      fusionCompleteSourceSum U P J ≤
        (D * (2 : ℝ) ^ (eta * b)) *
            completeQuotientWeight (R := R) J +
          T * (2 : ℝ) ^ (theta * b)) :
    (Nat.card
        (FusionOrbitFamily U (FusionAcceptedOrbitPredicate U P)) : ℝ) /
        exactBenchmark (b + w) ≤
      growingQuotientHotKernel (fun n => (subgroupCount n : ℝ))
          b w v D
          (Nat.card
            (Subgroup.normalizer
              (U : Set (Equiv.Perm (Fin w)))) : ℝ)
          eta delta c +
        fusionWidthColdKernel b w D
          (Nat.card
            (Subgroup.normalizer
              (U : Set (Equiv.Perm (Fin w)))) : ℝ)
          (eta + c) * ((subgroupCount b : ℝ) / exactBenchmark b) +
        fusionWidthColdKernel b w T
          (Nat.card
            (Subgroup.normalizer
              (U : Set (Equiv.Perm (Fin w)))) : ℝ)
          theta * ((subgroupCount b : ℝ) / exactBenchmark b) := by
  let q := growingQuotientMoment delta (v : ℝ) (b : ℝ)
  let A : ℝ := Nat.card
    (Subgroup.normalizer (U : Set (Equiv.Perm (Fin w))))
  have hq : 1 ≤ q := growingQuotientMoment_pos delta (v : ℝ) (b : ℝ)
  have hmain : 0 ≤ D * (2 : ℝ) ^ (eta * b) :=
    mul_nonneg hD (by positivity)
  have htail : 0 ≤ T * (2 : ℝ) ^ (theta * b) :=
    mul_nonneg hT (by positivity)
  have ht := growingQuotientThreshold_pos c b
  have hbound :=
    fusionPhysical_completeQuotient_additiveTail_normalized_bound
      U P hP rhoR hrhoR
      (D * (2 : ℝ) ^ (eta * b))
      (T * (2 : ℝ) ^ (theta * b))
      (growingQuotientThreshold c b) hmain htail ht hq henvelope
  change _ ≤
    growingQuotientHotKernel (fun n => (subgroupCount n : ℝ))
        b w v D A eta delta c +
      fusionWidthColdKernel b w D A (eta + c) *
        ((subgroupCount b : ℝ) / exactBenchmark b) +
      fusionWidthColdKernel b w T A theta *
        ((subgroupCount b : ℝ) / exactBenchmark b)
  calc
    _ ≤ growingQuotientNormalizedPointing b w A *
        (D * (2 : ℝ) ^ (eta * b) /
              growingQuotientThreshold c b ^ (q - 1) *
              (subgroupCount (b + q * v) : ℝ) +
          (subgroupCount b : ℝ) * D * (2 : ℝ) ^ (eta * b) *
              growingQuotientThreshold c b +
          (subgroupCount b : ℝ) * T * (2 : ℝ) ^ (theta * b)) := by
      simpa only [q, A, mul_assoc] using hbound
    _ = growingQuotientNormalizedPointing b w A *
          (D * (2 : ℝ) ^ (eta * b) /
              growingQuotientThreshold c b ^ (q - 1) *
              (subgroupCount (b + q * v) : ℝ)) +
        growingQuotientNormalizedPointing b w A *
          ((subgroupCount b : ℝ) * D * (2 : ℝ) ^ (eta * b) *
              growingQuotientThreshold c b) +
        growingQuotientNormalizedPointing b w A *
          ((subgroupCount b : ℝ) * T * (2 : ℝ) ^ (theta * b)) := by
      ring
    _ = _ := by
      rw [show growingQuotientNormalizedPointing b w A *
          (D * (2 : ℝ) ^ (eta * b) /
              growingQuotientThreshold c b ^ (q - 1) *
              (subgroupCount (b + q * v) : ℝ)) =
            growingQuotientHotKernel (fun n => (subgroupCount n : ℝ))
              b w v D A eta delta c by
        simpa only [q, growingQuotientGraphDegree] using
          growingQuotient_hot_identity
            (fun n => (subgroupCount n : ℝ))
            b w v D A eta delta c]
      rw [growingQuotient_cold_identity (subgroupCount b : ℝ)
        b w D A eta c]
      rw [show growingQuotientNormalizedPointing b w A *
          ((subgroupCount b : ℝ) * T * (2 : ℝ) ^ (theta * b)) =
            fusionWidthColdKernel b w T A theta *
              ((subgroupCount b : ℝ) / exactBenchmark b) by
        simpa only [growingQuotientThreshold, zero_mul, Real.rpow_zero,
          mul_one, add_zero] using
          (growingQuotient_cold_identity (subgroupCount b : ℝ)
            b w T A theta 0)]

/-- Exact local physical bound with the additive tail retained as a second
cold coefficient. -/
def GrowingQuotientAdditiveTailLocalPhysicalBound
    (w0 : ℕ)
    (U : ∀ w, ι w → Subgroup (Equiv.Perm (Fin w)))
    (P : ∀ w (i : ι w) b,
      Subgroup (U w i × Equiv.Perm (Fin b)) → Prop)
    (D T : ∀ w, ι w → ℕ → ℝ) (A : ∀ w, ι w → ℝ)
    (v : ∀ w, ι w → ℕ) (eta delta c alpha theta : ∀ w, ι w → ℝ) : Prop :=
  ∀ n (j : GrowingQuotientPhysicalIndex (ι := ι) w0 n),
    (Nat.card (GrowingQuotientCanonicalFamily w0 n U P j) : ℝ) /
        exactBenchmark n ≤
      growingQuotientHotKernel (fun m => (subgroupCount m : ℝ))
          (n - j.1.1) j.1.1 (v j.1.1 j.2)
          (D j.1.1 j.2 (n - j.1.1)) (A j.1.1 j.2)
          (eta j.1.1 j.2) (delta j.1.1 j.2) (c j.1.1 j.2) +
        fusionWidthColdKernel (n - j.1.1) j.1.1
          (D j.1.1 j.2 (n - j.1.1)) (A j.1.1 j.2)
          (alpha j.1.1 j.2) * ordinarySubgroupRatio (n - j.1.1) +
        fusionWidthColdKernel (n - j.1.1) j.1.1
          (T j.1.1 j.2 (n - j.1.1)) (A j.1.1 j.2)
          (theta j.1.1 j.2) * ordinarySubgroupRatio (n - j.1.1)

/-- An additive complete-source envelope supplies the exact local physical
bound. -/
theorem growingQuotientAdditiveTailLocalPhysicalBound_of_completeSource
    (w0 : ℕ)
    (U : ∀ w, ι w → Subgroup (Equiv.Perm (Fin w)))
    (P : ∀ w (i : ι w) b,
      Subgroup (U w i × Equiv.Perm (Fin b)) → Prop)
    (R : ∀ w, ι w → Type*)
    [∀ w i, Group (R w i)] [∀ w i, Finite (R w i)]
    (D T : ∀ w, ι w → ℕ → ℝ) (A : ∀ w, ι w → ℝ)
    (v : ∀ w, ι w → ℕ) (eta delta c alpha theta : ∀ w, ι w → ℝ)
    (rhoR : ∀ w i, R w i →* Equiv.Perm (Fin (v w i)))
    (hrhoR : ∀ w i, Function.Injective (rhoR w i))
    (hP : ∀ w i b, FusionOrbitNatural (U w i) (P w i b))
    (hD : ∀ w i b, 0 ≤ D w i b) (hT : ∀ w i b, 0 ≤ T w i b)
    (hA : ∀ w i, A w i =
      (Nat.card (Subgroup.normalizer
        (U w i : Set (Equiv.Perm (Fin w)))) : ℝ))
    (halpha : ∀ w i, alpha w i = eta w i + c w i)
    (henvelope : ∀ w i b (J : Subgroup (Equiv.Perm (Fin b))),
      fusionCompleteSourceSum (U w i) (P w i b) J ≤
        (D w i b * (2 : ℝ) ^ (eta w i * b)) *
            completeQuotientWeight (R := R w i) J +
          T w i b * (2 : ℝ) ^ (theta w i * b)) :
    GrowingQuotientAdditiveTailLocalPhysicalBound
      w0 U P D T A v eta delta c alpha theta := by
  intro n j
  let w : ℕ := j.1.1
  let i : ι w := j.2
  have hwn : w ≤ n := growingQuotientPhysicalWidth_le j
  have hbound := fusionPhysical_growingQuotient_additiveTail_kernel_bound
    (U w i) (P w i (n - w)) (hP w i (n - w))
    (rhoR w i) (hrhoR w i)
    (D w i (n - w)) (T w i (n - w))
    (eta w i) (theta w i) (delta w i) (c w i)
    (hD w i (n - w)) (hT w i (n - w))
    (henvelope w i (n - w))
  rw [GrowingQuotientCanonicalFamily, fusionWidthCanonicalFamily_card]
  simpa only [w, i, Nat.sub_add_cancel hwn, ordinarySubgroupRatio,
    hA w i, halpha w i] using hbound

/-- Global physical premise with one growing-comparator row and one pure
additive cold row. -/
def GrowingQuotientAdditiveTailPhysicalBound
    (error : ℕ → ℝ) (w0 : ℕ)
    (D T : ∀ w, ι w → ℕ → ℝ) (A : ∀ w, ι w → ℝ)
    (v : ∀ w, ι w → ℕ) (eta delta c alpha theta : ∀ w, ι w → ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop,
    error n ≤
      growingQuotientHotTotal (fun m => (subgroupCount m : ℝ))
        w0 n D A v eta delta c +
      (∑ b ∈ Finset.range n,
        growingQuotientColdRow w0 D A alpha n b * ordinarySubgroupRatio b) +
      ∑ b ∈ Finset.range n,
        growingQuotientColdRow w0 T A theta n b * ordinarySubgroupRatio b

private theorem sum_Ico_subtype_additiveTail {w0 n : ℕ} (f : ℕ → ℝ) :
    (∑ w : {w : ℕ // w ∈ Finset.Ico w0 (n + 1)}, f w.1) =
      ∑ w ∈ Finset.Ico w0 (n + 1), f w := by
  exact (Finset.sum_subtype (Finset.Ico w0 (n + 1))
    (fun _ => Iff.rfl) f).symm

/-- A literal cover and additive local estimates assemble into the exact
three-term physical premise. -/
theorem growingQuotientAdditiveTailPhysicalBound_of_local
    (error : ℕ → ℝ) (w0 : ℕ) (hw0 : 1 ≤ w0)
    (F : ∀ n, Set (Subgroup (Equiv.Perm (Fin n))))
    (U : ∀ w, ι w → Subgroup (Equiv.Perm (Fin w)))
    (P : ∀ w (i : ι w) b,
      Subgroup (U w i × Equiv.Perm (Fin b)) → Prop)
    (D T : ∀ w, ι w → ℕ → ℝ) (A : ∀ w, ι w → ℝ)
    (v : ∀ w, ι w → ℕ) (eta delta c alpha theta : ∀ w, ι w → ℝ)
    (herror : ∀ᶠ n : ℕ in atTop,
      error n ≤ (Nat.card (F n) : ℝ) / exactBenchmark n)
    (hcover : ∀ n H, H ∈ F n →
      ∃ j : GrowingQuotientPhysicalIndex (ι := ι) w0 n,
        H ∈ GrowingQuotientCanonicalFamily w0 n U P j)
    (hlocal : GrowingQuotientAdditiveTailLocalPhysicalBound
      w0 U P D T A v eta delta c alpha theta) :
    GrowingQuotientAdditiveTailPhysicalBound
      error w0 D T A v eta delta c alpha theta := by
  filter_upwards [herror] with n herrorn
  have hcard := fusionPhysicalUnion_card_le (F n)
    (fun j : GrowingQuotientPhysicalIndex (ι := ι) w0 n =>
      GrowingQuotientCanonicalFamily w0 n U P j) (hcover n)
  have hcardR : (Nat.card (F n) : ℝ) ≤
      ∑ j : GrowingQuotientPhysicalIndex (ι := ι) w0 n,
        (Nat.card (GrowingQuotientCanonicalFamily w0 n U P j) : ℝ) := by
    exact_mod_cast hcard
  apply herrorn.trans
  calc
    (Nat.card (F n) : ℝ) / exactBenchmark n ≤
        (∑ j : GrowingQuotientPhysicalIndex (ι := ι) w0 n,
          (Nat.card (GrowingQuotientCanonicalFamily w0 n U P j) : ℝ)) /
            exactBenchmark n :=
      div_le_div_of_nonneg_right hcardR (exactBenchmark_pos n).le
    _ = ∑ j : GrowingQuotientPhysicalIndex (ι := ι) w0 n,
        (Nat.card (GrowingQuotientCanonicalFamily w0 n U P j) : ℝ) /
          exactBenchmark n := Finset.sum_div _ _ _
    _ ≤ ∑ j : GrowingQuotientPhysicalIndex (ι := ι) w0 n,
        (growingQuotientHotKernel (fun m => (subgroupCount m : ℝ))
            (n - j.1.1) j.1.1 (v j.1.1 j.2)
            (D j.1.1 j.2 (n - j.1.1)) (A j.1.1 j.2)
            (eta j.1.1 j.2) (delta j.1.1 j.2) (c j.1.1 j.2) +
          fusionWidthColdKernel (n - j.1.1) j.1.1
            (D j.1.1 j.2 (n - j.1.1)) (A j.1.1 j.2)
            (alpha j.1.1 j.2) * ordinarySubgroupRatio (n - j.1.1) +
          fusionWidthColdKernel (n - j.1.1) j.1.1
            (T j.1.1 j.2 (n - j.1.1)) (A j.1.1 j.2)
            (theta j.1.1 j.2) * ordinarySubgroupRatio (n - j.1.1)) :=
      Finset.sum_le_sum (fun j _ => hlocal n j)
    _ = growingQuotientHotTotal (fun m => (subgroupCount m : ℝ))
          w0 n D A v eta delta c +
        (∑ b ∈ Finset.range n,
          growingQuotientColdRow w0 D A alpha n b * ordinarySubgroupRatio b) +
        ∑ b ∈ Finset.range n,
          growingQuotientColdRow w0 T A theta n b * ordinarySubgroupRatio b := by
      simp only [Finset.sum_add_distrib]
      rw [Fintype.sum_sigma, Fintype.sum_sigma, Fintype.sum_sigma]
      rw [growingQuotientColdRow_weighted_sum w0 hw0
        D A alpha ordinarySubgroupRatio n]
      rw [growingQuotientColdRow_weighted_sum w0 hw0
        T A theta ordinarySubgroupRatio n]
      let hot : ℕ → ℝ := fun w => ∑ i,
        growingQuotientHotKernel (fun m => (subgroupCount m : ℝ))
          (n - w) w (v w i) (D w i (n - w)) (A w i)
          (eta w i) (delta w i) (c w i)
      let cold : ℕ → ℝ := fun w => (∑ i,
        fusionWidthColdKernel (n - w) w (D w i (n - w))
          (A w i) (alpha w i)) * ordinarySubgroupRatio (n - w)
      let tail : ℕ → ℝ := fun w => (∑ i,
        fusionWidthColdKernel (n - w) w (T w i (n - w))
          (A w i) (theta w i)) * ordinarySubgroupRatio (n - w)
      have hhot := sum_Ico_subtype_additiveTail
        (w0 := w0) (n := n) hot
      have hcold := sum_Ico_subtype_additiveTail
        (w0 := w0) (n := n) cold
      have htail := sum_Ico_subtype_additiveTail
        (w0 := w0) (n := n) tail
      simpa only [hot, cold, tail, growingQuotientHotTotal,
        growingQuotientColdWidthSum, Finset.sum_mul] using
          congrArg₂ (fun x y => x + y.1 + y.2) hhot
            (congrArg₂ Prod.mk hcold htail)

/-- The additive physical premise closes by combining the usual growing
quotient estimate with a cold-only estimate for the tail. -/
noncomputable def growingQuotientAdditiveTail_exponentialForwardEstimate
    (error : ℕ → ℝ) {rho : ℝ} (w0 : ℕ)
    (D T : ∀ w, ι w → ℕ → ℝ) (A : ∀ w, ι w → ℝ)
    (v : ∀ w, ι w → ℕ) (eta delta c alpha theta : ∀ w, ι w → ℝ)
    (hrho : 0 < rho) (hrho8 : rho ≤ 1 / 8) (hw0 : 3 ≤ w0)
    (hD : ∀ w i b, 0 ≤ D w i b) (hT : ∀ w i b, 0 ≤ T w i b)
    (hA : ∀ w i, 0 < A w i)
    (hparameters : GrowingQuotientParameterBound rho v eta delta c alpha)
    (htailGap : ∀ w i,
      theta w i ≤ (halfDegree w : ℝ) / 4 - rho * w / 4)
    (hmass : GrowingMenuMassBound w0 D A)
    (htailMass : GrowingMenuMassBound w0 T A)
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ)))
    (hphysical : GrowingQuotientAdditiveTailPhysicalBound
      error w0 D T A v eta delta c alpha theta) :
    OrdinaryFrontierClosure.ExponentialForwardEstimate error := by
  let mainError : ℕ → ℝ := fun n =>
    growingQuotientHotTotal (fun m => (subgroupCount m : ℝ))
        w0 n D A v eta delta c +
      ∑ b ∈ Finset.range n,
        growingQuotientColdRow w0 D A alpha n b * ordinarySubgroupRatio b
  let tailError : ℕ → ℝ := fun n =>
    ∑ b ∈ Finset.range n,
      growingQuotientColdRow w0 T A theta n b * ordinarySubgroupRatio b
  have hmainPhysical : GrowingQuotientPhysicalBound
      mainError w0 D A v eta delta c alpha :=
    Filter.Eventually.of_forall (fun _ => le_rfl)
  have htailPhysical : GrowingColdOnlyPhysicalBound
      tailError w0 T A theta :=
    Filter.Eventually.of_forall (fun _ => le_rfl)
  let Emain := growingQuotient_exponentialForwardEstimate
    mainError w0 D A v eta delta c alpha hrho hrho8 hw0 hD hA
      hparameters hmass hcoarse hmainPhysical
  let Etail := growingColdOnly_exponentialForwardEstimate
    tailError w0 T A theta hrho hrho8 hw0 hT hA htailGap
      htailMass htailPhysical
  let E := OrdinaryFrontierClosure.ExponentialForwardEstimate.add Emain Etail
  let N : ℕ := Classical.choose (eventually_atTop.mp hphysical)
  have hN := Classical.choose_spec (eventually_atTop.mp hphysical)
  exact OrdinaryFrontierClosure.ExponentialForwardEstimate.of_le E N
    (fun n hn => by
      simpa only [mainError, tailError, add_assoc] using hN n hn)

end SymmetricSubgroupAsymptotics

end
