import SymmetricSubgroupAsymptotics.GrowingQuotientAdditiveTail

/-!
# Growing quotient transfer with source-summed exceptional scalars

Most physical cells enter through a complete-comparator envelope and an
optional source-independent cold tail.  Rank-tail cells instead yield a
bound only after summing over all complete sources.  This file lets a single
literal physical cover use both forms: every local cell has the usual three
comparator terms plus an exceptional scalar, and the exceptional scalars are
summed over the original width/action menu before their exponential decay is
invoked.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

variable {ι : ℕ → Type*} [∀ w, Fintype (ι w)]

/-- An eventual exponential scalar bound, in the exact form needed to make a
zero-kernel forward estimate. -/
structure ExponentialScalarBound (S : ℕ → ℝ) where
  threshold : ℕ
  rate : ℝ
  constant : ℝ
  rate_pos : 0 < rate
  constant_pos : 0 < constant
  bound : ∀ n, threshold ≤ n →
    S n ≤ constant * (2 : ℝ) ^ (-rate * (n : ℝ))

/-- A decaying scalar is already a complete forward estimate, with no
continuation row. -/
def ExponentialScalarBound.toForwardEstimate {S : ℕ → ℝ}
    (E : ExponentialScalarBound S) :
    OrdinaryFrontierClosure.ExponentialForwardEstimate S where
  scalar := S
  kernel := fun _ _ => 0
  threshold := E.threshold
  rate := E.rate
  scalarConst := E.constant
  rowConst := 0
  rate_pos := E.rate_pos
  scalarConst_pos := E.constant_pos
  rowConst_nonneg := le_rfl
  kernel_nonneg := by simp
  recurrence := by simp
  scalar_decay := E.bound
  row_decay := by simp

/-- Exceptional contribution summed over the literal growing width/action
menu.  The complement degree is `n-w`, exactly as in the physical cover. -/
def growingQuotientExceptionalTotal
    (w0 : ℕ) (X : ∀ w, ι w → ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ w ∈ Finset.Ico w0 (n + 1), ∑ i, X w i (n - w)

/-- Local physical inequality with an additional source-summed exceptional
scalar.  Ordinary cells set `X = 0`; rank-tail cells set the three comparator
coefficients to zero and retain their already-summed physical bound in `X`. -/
def GrowingQuotientAdditiveExceptionalLocalPhysicalBound
    (w0 : ℕ)
    (U : ∀ w, ι w → Subgroup (Equiv.Perm (Fin w)))
    (P : ∀ w (i : ι w) b,
      Subgroup (U w i × Equiv.Perm (Fin b)) → Prop)
    (D T X : ∀ w, ι w → ℕ → ℝ) (A : ∀ w, ι w → ℝ)
    (v : ∀ w, ι w → ℕ)
    (eta delta c alpha theta : ∀ w, ι w → ℝ) : Prop :=
  ∀ n (j : GrowingQuotientPhysicalIndex (ι := ι) w0 n),
    (Nat.card (GrowingQuotientCanonicalFamily w0 n U P j) : ℝ) /
        exactBenchmark n ≤
      (growingQuotientHotKernel (fun m => (subgroupCount m : ℝ))
          (n - j.1.1) j.1.1 (v j.1.1 j.2)
          (D j.1.1 j.2 (n - j.1.1)) (A j.1.1 j.2)
          (eta j.1.1 j.2) (delta j.1.1 j.2) (c j.1.1 j.2) +
        fusionWidthColdKernel (n - j.1.1) j.1.1
          (D j.1.1 j.2 (n - j.1.1)) (A j.1.1 j.2)
          (alpha j.1.1 j.2) * ordinarySubgroupRatio (n - j.1.1) +
        fusionWidthColdKernel (n - j.1.1) j.1.1
          (T j.1.1 j.2 (n - j.1.1)) (A j.1.1 j.2)
          (theta j.1.1 j.2) * ordinarySubgroupRatio (n - j.1.1)) +
        X j.1.1 j.2 (n - j.1.1)

/-- Global physical premise with the exceptional menu sum kept as a separate
scalar. -/
def GrowingQuotientAdditiveExceptionalPhysicalBound
    (error : ℕ → ℝ) (w0 : ℕ)
    (D T X : ∀ w, ι w → ℕ → ℝ) (A : ∀ w, ι w → ℝ)
    (v : ∀ w, ι w → ℕ)
    (eta delta c alpha theta : ∀ w, ι w → ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop,
    error n ≤
      (growingQuotientHotTotal (fun m => (subgroupCount m : ℝ))
          w0 n D A v eta delta c +
        (∑ b ∈ Finset.range n,
          growingQuotientColdRow w0 D A alpha n b * ordinarySubgroupRatio b) +
        ∑ b ∈ Finset.range n,
          growingQuotientColdRow w0 T A theta n b * ordinarySubgroupRatio b) +
      growingQuotientExceptionalTotal w0 X n

private theorem sum_Ico_subtype_exceptional {w0 n : ℕ} (f : ℕ → ℝ) :
    (∑ w : {w : ℕ // w ∈ Finset.Ico w0 (n + 1)}, f w.1) =
      ∑ w ∈ Finset.Ico w0 (n + 1), f w := by
  exact (Finset.sum_subtype (Finset.Ico w0 (n + 1))
    (fun _ => Iff.rfl) f).symm

/-- Literal coverage and the four-term local estimate assemble into the
global comparator recurrence plus exceptional scalar. -/
theorem growingQuotientAdditiveExceptionalPhysicalBound_of_local
    (error : ℕ → ℝ) (w0 : ℕ) (hw0 : 1 ≤ w0)
    (F : ∀ n, Set (Subgroup (Equiv.Perm (Fin n))))
    (U : ∀ w, ι w → Subgroup (Equiv.Perm (Fin w)))
    (P : ∀ w (i : ι w) b,
      Subgroup (U w i × Equiv.Perm (Fin b)) → Prop)
    (D T X : ∀ w, ι w → ℕ → ℝ) (A : ∀ w, ι w → ℝ)
    (v : ∀ w, ι w → ℕ)
    (eta delta c alpha theta : ∀ w, ι w → ℝ)
    (herror : ∀ᶠ n : ℕ in atTop,
      error n ≤ (Nat.card (F n) : ℝ) / exactBenchmark n)
    (hcover : ∀ n H, H ∈ F n →
      ∃ j : GrowingQuotientPhysicalIndex (ι := ι) w0 n,
        H ∈ GrowingQuotientCanonicalFamily w0 n U P j)
    (hlocal : GrowingQuotientAdditiveExceptionalLocalPhysicalBound
      w0 U P D T X A v eta delta c alpha theta) :
    GrowingQuotientAdditiveExceptionalPhysicalBound
      error w0 D T X A v eta delta c alpha theta := by
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
        ((growingQuotientHotKernel (fun m => (subgroupCount m : ℝ))
            (n - j.1.1) j.1.1 (v j.1.1 j.2)
            (D j.1.1 j.2 (n - j.1.1)) (A j.1.1 j.2)
            (eta j.1.1 j.2) (delta j.1.1 j.2) (c j.1.1 j.2) +
          fusionWidthColdKernel (n - j.1.1) j.1.1
            (D j.1.1 j.2 (n - j.1.1)) (A j.1.1 j.2)
            (alpha j.1.1 j.2) * ordinarySubgroupRatio (n - j.1.1) +
          fusionWidthColdKernel (n - j.1.1) j.1.1
            (T j.1.1 j.2 (n - j.1.1)) (A j.1.1 j.2)
            (theta j.1.1 j.2) * ordinarySubgroupRatio (n - j.1.1)) +
          X j.1.1 j.2 (n - j.1.1)) :=
      Finset.sum_le_sum (fun j _ => hlocal n j)
    _ = (growingQuotientHotTotal (fun m => (subgroupCount m : ℝ))
          w0 n D A v eta delta c +
        (∑ b ∈ Finset.range n,
          growingQuotientColdRow w0 D A alpha n b * ordinarySubgroupRatio b) +
        ∑ b ∈ Finset.range n,
          growingQuotientColdRow w0 T A theta n b * ordinarySubgroupRatio b) +
        growingQuotientExceptionalTotal w0 X n := by
      simp only [Finset.sum_add_distrib]
      rw [Fintype.sum_sigma, Fintype.sum_sigma, Fintype.sum_sigma,
        Fintype.sum_sigma]
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
      let exceptional : ℕ → ℝ := fun w => ∑ i, X w i (n - w)
      have hhot := sum_Ico_subtype_exceptional
        (w0 := w0) (n := n) hot
      have hcold := sum_Ico_subtype_exceptional
        (w0 := w0) (n := n) cold
      have htail := sum_Ico_subtype_exceptional
        (w0 := w0) (n := n) tail
      have hexceptional := sum_Ico_subtype_exceptional
        (w0 := w0) (n := n) exceptional
      simpa only [hot, cold, tail, exceptional, growingQuotientHotTotal,
        growingQuotientColdWidthSum, growingQuotientExceptionalTotal,
        Finset.sum_mul] using
          congrArg₂ (fun x y => (x + y.1.1 + y.1.2) + y.2) hhot
            (congrArg₂ Prod.mk (congrArg₂ Prod.mk hcold htail) hexceptional)

/-- The exceptional scalar adds to the already proved comparator/tail
forward estimate.  No source moment is reapplied after the exceptional term
has been formed. -/
noncomputable def
    growingQuotientAdditiveExceptional_exponentialForwardEstimate
    (error : ℕ → ℝ) {rho : ℝ} (w0 : ℕ)
    (D T X : ∀ w, ι w → ℕ → ℝ) (A : ∀ w, ι w → ℝ)
    (v : ∀ w, ι w → ℕ)
    (eta delta c alpha theta : ∀ w, ι w → ℝ)
    (hrho : 0 < rho) (hrho8 : rho ≤ 1 / 8) (hw0 : 3 ≤ w0)
    (hD : ∀ w i b, 0 ≤ D w i b) (hT : ∀ w i b, 0 ≤ T w i b)
    (hA : ∀ w i, 0 < A w i)
    (hparameters : GrowingQuotientParameterBound rho v eta delta c alpha)
    (htailGap : ∀ w i,
      theta w i ≤ (halfDegree w : ℝ) / 4 - rho * w / 4)
    (hmass : GrowingMenuMassBound w0 D A)
    (htailMass : GrowingMenuMassBound w0 T A)
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ)))
    (hexceptional : ExponentialScalarBound
      (growingQuotientExceptionalTotal w0 X))
    (hphysical : GrowingQuotientAdditiveExceptionalPhysicalBound
      error w0 D T X A v eta delta c alpha theta) :
    OrdinaryFrontierClosure.ExponentialForwardEstimate error := by
  let regularError : ℕ → ℝ := fun n =>
    growingQuotientHotTotal (fun m => (subgroupCount m : ℝ))
        w0 n D A v eta delta c +
      (∑ b ∈ Finset.range n,
        growingQuotientColdRow w0 D A alpha n b * ordinarySubgroupRatio b) +
      ∑ b ∈ Finset.range n,
        growingQuotientColdRow w0 T A theta n b * ordinarySubgroupRatio b
  have hregularPhysical : GrowingQuotientAdditiveTailPhysicalBound
      regularError w0 D T A v eta delta c alpha theta :=
    Filter.Eventually.of_forall (fun _ => le_rfl)
  let Eregular := growingQuotientAdditiveTail_exponentialForwardEstimate
    regularError w0 D T A v eta delta c alpha theta hrho hrho8 hw0
      hD hT hA hparameters htailGap hmass htailMass hcoarse
      hregularPhysical
  let Eexceptional := hexceptional.toForwardEstimate
  let E := OrdinaryFrontierClosure.ExponentialForwardEstimate.add
    Eregular Eexceptional
  let N : ℕ := Classical.choose (eventually_atTop.mp hphysical)
  have hN := Classical.choose_spec (eventually_atTop.mp hphysical)
  exact OrdinaryFrontierClosure.ExponentialForwardEstimate.of_le E N
    (fun n hn => by
      simpa only [regularError, add_assoc] using hN n hn)

end SymmetricSubgroupAsymptotics

end
