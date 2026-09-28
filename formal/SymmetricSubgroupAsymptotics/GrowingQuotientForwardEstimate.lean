import SymmetricSubgroupAsymptotics.GrowingMenuMassAbsorption
import SymmetricSubgroupAsymptotics.ForwardEstimateAlgebra

/-!
# Complete forward estimates from a growing comparator menu

This is the reusable numerical endpoint of the growing complete-quotient
transfer.  A caller supplies one physical inequality with every original
weight retained.  The theorem below derives a single exponentially
contractive forward estimate from the original margin, the direct weighted
menu-mass condition, and the published coarse subgroup bound.

The nontrivial and trivial comparator branches are kept separate.  A
nontrivial comparator is padded and contributes both a hot scalar and a cold
row.  A trivial comparator has empty hot part and enters through the
cold-only constructor, so no artificial lower bound on its degree is used.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

open OrdinaryFrontierClosure

variable {ι : ℕ → Type*} [∀ w, Fintype (ι w)]

/-- All numerical conditions used by the aggregated hot and cold estimates. -/
structure GrowingQuotientParameterBound (ρ : ℝ)
    (v : ∀ w, ι w → ℕ) (η δ c α : ∀ w, ι w → ℝ) : Prop where
  delta_nonneg : ∀ w i, 0 ≤ δ w i
  degree_pos : ∀ w i, 0 < v w i
  ratio : ∀ w i, ρ / 2 ≤ δ w i / (v w i : ℝ)
  degree_upper : ∀ w i, (v w i : ℝ) ≤ (1 - 4 * ρ) * w
  delta_lower : ∀ w i, ρ * w / 2 ≤ δ w i
  hot_margin : ∀ w i, η w i + c w i - w / 8 ≤ -δ w i / 2
  threshold_eq : ∀ w i, c w i = (v w i : ℝ) / 8 + δ w i / 2
  delta_upper : ∀ w i, δ w i ≤ (w : ℝ) / 8
  degree_lower : ∀ w i, ρ * w ≤ (v w i : ℝ)
  degree_width : ∀ w i, (v w i : ℝ) ≤ w
  cold_slope : ∀ w i, α w i = η w i + c w i
  cold_gap : ∀ w i,
    α w i ≤ (halfDegree w : ℝ) / 4 - ρ * w / 4

/-- The controlled padding of an original nontrivial faithful comparator
supplies every numerical condition in `GrowingQuotientParameterBound`. -/
theorem growingPadded_parameterBound
    {ρ : ℝ} (v₀ : ∀ w, ι w → ℕ) (η : ∀ w, ι w → ℝ)
    (hρ : 0 < ρ) (hρ8 : ρ ≤ 1 / 8)
    (hη : ∀ w i, 0 ≤ η w i) (hv₀ : ∀ w i, 2 ≤ v₀ w i)
    (hmargin : ∀ w i,
      ρ * w ≤ ((evenWidth w : ℝ) - v₀ w i) / 8 - η w i) :
    GrowingQuotientParameterBound ρ
      (fun w i => paddedComparatorDegree ρ (v₀ w i) w) η
      (fun w i => paddedComparatorDelta ρ (η w i) (v₀ w i) w)
      (fun w i =>
        (paddedComparatorDegree ρ (v₀ w i) w : ℝ) / 8 +
          paddedComparatorDelta ρ (η w i) (v₀ w i) w / 2)
      (fun w i => η w i +
        ((paddedComparatorDegree ρ (v₀ w i) w : ℝ) / 8 +
          paddedComparatorDelta ρ (η w i) (v₀ w i) w / 2)) := by
  let v : ∀ w, ι w → ℕ :=
    fun w i => paddedComparatorDegree ρ (v₀ w i) w
  let δ : ∀ w, ι w → ℝ :=
    fun w i => paddedComparatorDelta ρ (η w i) (v₀ w i) w
  let c : ∀ w, ι w → ℝ :=
    fun w i => (v w i : ℝ) / 8 + δ w i / 2
  let α : ∀ w, ι w → ℝ := fun w i => η w i + c w i
  change GrowingQuotientParameterBound ρ v η δ c α
  have hparam (w : ℕ) (i : ι w) :
      ρ * w ≤ (v w i : ℝ) ∧
        (v w i : ℝ) ≤ (1 - 4 * ρ) * w ∧ ρ * w / 2 ≤ δ w i := by
    simpa only [v, δ] using paddedComparator_parameters hρ hρ8
      (hη w i) (hv₀ w i) (hmargin w i)
  refine
    { delta_nonneg := ?_, degree_pos := ?_, ratio := ?_,
      degree_upper := ?_, delta_lower := ?_, hot_margin := ?_,
      threshold_eq := ?_, delta_upper := ?_, degree_lower := ?_,
      degree_width := ?_, cold_slope := ?_, cold_gap := ?_ }
  · intro w i
    exact (hparam w i).2.2.trans' (by positivity)
  · intro w i
    have hv₂ : 2 ≤ v w i := by
      dsimp [v, paddedComparatorDegree]
      exact (hv₀ w i).trans (le_max_left _ _)
    omega
  · intro w i
    have hvpos : (0 : ℝ) < v w i := by
      exact_mod_cast (show 0 < v w i by
        have := hv₀ w i
        dsimp [v, paddedComparatorDegree]
        omega)
    apply (le_div_iff₀ hvpos).2
    have hvw : (v w i : ℝ) ≤ w := by
      calc
        (v w i : ℝ) ≤ (1 - 4 * ρ) * w := (hparam w i).2.1
        _ ≤ w := by
          have hw0 : (0 : ℝ) ≤ w := by positivity
          nlinarith [mul_nonneg hρ.le hw0]
    have hm := mul_le_mul_of_nonneg_left hvw (show 0 ≤ ρ / 2 by positivity)
    nlinarith [(hparam w i).2.2]
  · intro w i
    exact (hparam w i).2.1
  · intro w i
    exact (hparam w i).2.2
  · intro w i
    have hew : (evenWidth w : ℝ) ≤ w := by
      exact_mod_cast evenWidth_le w
    dsimp [c, δ, paddedComparatorDelta]
    nlinarith
  · intro w i
    rfl
  · intro w i
    have hew : (evenWidth w : ℝ) ≤ w := by
      exact_mod_cast evenWidth_le w
    have hv0 : (0 : ℝ) ≤ v w i := by positivity
    dsimp [δ, paddedComparatorDelta]
    nlinarith [hη w i]
  · intro w i
    exact (hparam w i).1
  · intro w i
    calc
      (v w i : ℝ) ≤ (1 - 4 * ρ) * w := (hparam w i).2.1
      _ ≤ w := by
        have hw0 : (0 : ℝ) ≤ w := by positivity
        nlinarith [mul_nonneg hρ.le hw0]
  · intro w i
    rfl
  · intro w i
    have heq : (evenWidth w : ℝ) = 2 * halfDegree w := by
      exact_mod_cast (show evenWidth w = 2 * halfDegree w by rfl)
    have hdeltaEq :
        δ w i = ((evenWidth w : ℝ) - v w i) / 8 - η w i := by
      rfl
    have hcoldEq :
        α w i = (halfDegree w : ℝ) / 4 - δ w i / 2 := by
      dsimp [α, c]
      rw [heq] at hdeltaEq
      nlinarith
    rw [hcoldEq]
    nlinarith [(hparam w i).2.2]

/-- Exact physical interface for a nontrivial growing menu.  It contains no
asymptotic estimate: the caller must prove this inequality from literal
orbit families and the complete quotient moment. -/
def GrowingQuotientPhysicalBound (error : ℕ → ℝ) (w₀ : ℕ)
    (D : ∀ w, ι w → ℕ → ℝ) (A : ∀ w, ι w → ℝ)
    (v : ∀ w, ι w → ℕ) (η δ c α : ∀ w, ι w → ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop,
    error n ≤
      growingQuotientHotTotal (fun m => (subgroupCount m : ℝ))
        w₀ n D A v η δ c +
      ∑ b ∈ Finset.range n,
        growingQuotientColdRow w₀ D A α n b * ordinarySubgroupRatio b

/-- Exact physical interface for a menu whose hot set is empty, in
particular for the trivial complete comparator. -/
def GrowingColdOnlyPhysicalBound (error : ℕ → ℝ) (w₀ : ℕ)
    (D : ∀ w, ι w → ℕ → ℝ) (A α : ∀ w, ι w → ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop,
    error n ≤ ∑ b ∈ Finset.range n,
      growingQuotientColdRow w₀ D A α n b * ordinarySubgroupRatio b

private theorem eventually_growing_ratio_half {ρ : ℝ} (hρ : 0 < ρ) :
    ∀ᶠ n : ℕ in atTop, (2 : ℝ) ^ (-ρ * n / 8) ≤ 1 / 2 := by
  have ha : 0 < ρ / 8 := by positivity
  filter_upwards [eventually_exponential_le_inv_rpow ha 1,
    eventually_ge_atTop 2] with n hexp hn
  have hexp' : (2 : ℝ) ^ (-ρ * n / 8) ≤ 1 / (n : ℝ) := by
    simpa [show -(ρ / 8) * (n : ℝ) = -ρ * n / 8 by ring] using hexp
  exact hexp'.trans (by
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    apply (div_le_iff₀ hnpos).2
    nlinarith)

private theorem eventually_growing_graph_coarse
    (s : ℕ → ℝ) (hs : FusionCoarseEstimate s)
    {ρ : ℝ} (w₀ : ℕ) (v : ∀ w, ι w → ℕ) (δ : ∀ w, ι w → ℝ)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hvlower : ∀ w i, ρ * w ≤ (v w i : ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ w, w ∈ Finset.Ico w₀ (n + 1) → ∀ i,
      s (growingQuotientGraphDegree (δ w i) (n - w) (v w i)) ≤
        (2 : ℝ) ^ ((1 / 16 + ε) *
          (growingQuotientGraphDegree (δ w i) (n - w) (v w i) : ℝ) ^ 2) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hs ε hε)
  filter_upwards [eventually_ge_atTop ⌈(N : ℝ) / ρ⌉₊] with n hn
  intro w hw i
  have hwn : w ≤ n := by
    have := (Finset.mem_Ico.mp hw).2
    omega
  have hnρ : (N : ℝ) / ρ ≤ n :=
    (Nat.le_ceil _).trans (by exact_mod_cast hn)
  have hNρ : (N : ℝ) ≤ ρ * n := by
    simpa [mul_comm] using (div_le_iff₀ hρ).mp hnρ
  have hdegree := growingQuotientGraphDegree_lower (δ := δ w i)
    (n - w) w (v w i)
    hρ1 (hvlower w i)
  have hnadd : n - w + w = n := Nat.sub_add_cancel hwn
  have hnaddR : ((n - w : ℕ) : ℝ) + w = n := by
    rw [← Nat.cast_add, hnadd]
  rw [hnaddR] at hdegree
  have hNM : N ≤ growingQuotientGraphDegree (δ w i) (n - w) (v w i) := by
    exact_mod_cast hNρ.trans hdegree
  exact hN _ hNM

/-- A complete nontrivial growing menu gives one exponentially contractive
forward estimate.  Padding may be installed by
`growingPadded_parameterBound`; the theorem itself also accepts any sharper
parameters satisfying the same invariant inequalities. -/
noncomputable def growingQuotient_exponentialForwardEstimate
    (error : ℕ → ℝ) {ρ : ℝ} (w₀ : ℕ)
    (D : ∀ w, ι w → ℕ → ℝ) (A : ∀ w, ι w → ℝ)
    (v : ∀ w, ι w → ℕ) (η δ c α : ∀ w, ι w → ℝ)
    (hρ : 0 < ρ) (hρ8 : ρ ≤ 1 / 8) (hw₀ : 3 ≤ w₀)
    (hD : ∀ w i b, 0 ≤ D w i b) (hA : ∀ w i, 0 < A w i)
    (hp : GrowingQuotientParameterBound ρ v η δ c α)
    (hmass : GrowingMenuMassBound w₀ D A)
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ)))
    (hphysical : GrowingQuotientPhysicalBound error w₀ D A v η δ c α) :
    ExponentialForwardEstimate error := by
  let L : ℝ := 1 + 1 / (2 * ρ)
  let ε : ℝ := ρ ^ 2 / (16 * L ^ 2)
  have hL : 0 < L := by dsimp [L]; positivity
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεbound : ε * L ^ 2 ≤ ρ ^ 2 / 16 := by
    dsimp [ε]
    field_simp [ne_of_gt hL]
    norm_num
  have hgraph := eventually_growing_graph_coarse
    (fun n => (subgroupCount n : ℝ)) hcoarse w₀ v δ hρ
      (hρ8.trans (by norm_num)) hp.degree_lower hε
  have hcold := growingMenuMass_cold_overhead w₀ D A hρ hw₀ hD hA hmass
  have hhot := growingMenuMass_hot_overhead w₀ D A hρ hD hA hmass
  have hratio := eventually_growing_ratio_half hρ
  have hall : ∀ᶠ n : ℕ in atTop,
      error n ≤
        growingQuotientHotTotal (fun m => (subgroupCount m : ℝ))
          w₀ n D A v η δ c +
        ∑ b ∈ Finset.range n,
          growingQuotientColdRow w₀ D A α n b * ordinarySubgroupRatio b ∧
      (∀ w, w ∈ Finset.Ico w₀ (n + 1) →
        eulerProduct⁻¹ ^ 2 * (((n + 1 : ℕ) : ℝ) ^ (w + 2)) *
            (2 : ℝ) ^ ((halfDegree w : ℝ) / 4 + 1 / 4) *
            (∑ i, D w i (n - w) / A w i) ≤
          (2 : ℝ) ^ (ρ * w * n / 16)) ∧
      eulerProduct⁻¹ * (((n + 1 : ℕ) : ℝ) ^ n) *
          (2 : ℝ) ^ (5 * (n : ℝ) / 8 + 1 / 4) *
          (∑ w ∈ Finset.Ico w₀ (n + 1), ∑ i, D w i (n - w) / A w i) ≤
        (2 : ℝ) ^ (ρ ^ 2 * (n : ℝ) ^ 2 / 16) ∧
      (∀ w, w ∈ Finset.Ico w₀ (n + 1) → ∀ i,
        (subgroupCount
          (growingQuotientGraphDegree (δ w i) (n - w) (v w i)) : ℝ) ≤
          (2 : ℝ) ^ ((1 / 16 + ε) *
            (growingQuotientGraphDegree (δ w i) (n - w) (v w i) : ℝ) ^ 2)) ∧
      (2 : ℝ) ^ (-ρ * n / 8) ≤ 1 / 2 := by
    filter_upwards [hphysical, hcold, hhot, hgraph, hratio] with
      n hphysicaln hcoldn hhotn hgraphn hration
    exact ⟨hphysicaln, hcoldn, hhotn, hgraphn, hration⟩
  let witness := eventually_atTop.mp hall
  let N : ℕ := Classical.choose witness
  have hN := Classical.choose_spec witness
  let N₀ := max 1 N
  let rate : ℝ := ρ ^ 2 / 8
  refine
    { scalar := fun n => growingQuotientHotTotal
        (fun m => (subgroupCount m : ℝ)) w₀ n D A v η δ c
      kernel := growingQuotientColdRow w₀ D A α
      threshold := N₀
      rate := rate
      scalarConst := 1
      rowConst := 2
      rate_pos := by dsimp [rate]; positivity
      scalarConst_pos := by norm_num
      rowConst_nonneg := by norm_num
      kernel_nonneg := ?_
      recurrence := ?_
      scalar_decay := ?_
      row_decay := ?_ }
  · intro n _ b _
    exact growingQuotientColdRow_nonneg w₀ D A α hD hA n b
  · intro n hn
    exact (hN n ((le_max_right 1 N).trans hn)).1
  · intro n hn
    have hn1 : 1 ≤ n := (le_max_left 1 N).trans hn
    obtain ⟨_, _, hhotn, hgraphn, _⟩ :=
      hN n ((le_max_right 1 N).trans hn)
    have hscalar := growingQuotientHotTotal_le
      (fun m => (subgroupCount m : ℝ)) w₀ n D A v η δ c
      hρ hρ8 (show 0 ≤ ε by exact hε.le) hD hA hp.delta_nonneg
      hp.degree_pos hp.ratio hp.degree_upper hp.delta_lower hp.hot_margin
      hp.threshold_eq hp.delta_upper hp.degree_lower hp.degree_width
      (by simpa only [L] using hεbound) hgraphn hhotn
    calc
      _ ≤ (2 : ℝ) ^ (-ρ ^ 2 * (n : ℝ) ^ 2 / 8) := hscalar
      _ ≤ 1 * (2 : ℝ) ^ (-rate * (n : ℝ)) := by
        rw [one_mul]
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        dsimp [rate]
        have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
        have hρsq : 0 ≤ ρ ^ 2 := sq_nonneg ρ
        nlinarith [mul_nonneg hρsq
          (mul_nonneg (show 0 ≤ (n : ℝ) by positivity)
            (sub_nonneg.mpr hnR))]
  · intro n hn
    obtain ⟨_, hcoldn, _, _, hration⟩ :=
      hN n ((le_max_right 1 N).trans hn)
    have hrow := growingQuotientColdRow_sum_le w₀ n D A α hρ hρ8 hw₀
      hD hA hp.cold_gap hcoldn hration
    have hrate : ρ ^ 2 ≤ ρ * w₀ := by
      have hwR : ρ ≤ (w₀ : ℝ) := by
        have : (3 : ℝ) ≤ w₀ := by exact_mod_cast hw₀
        nlinarith
      nlinarith [mul_nonneg hρ.le (sub_nonneg.mpr hwR)]
    calc
      _ ≤ 2 * (2 : ℝ) ^ (-ρ * w₀ * n / 8) := hrow
      _ ≤ 2 * (2 : ℝ) ^ (-rate * (n : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        dsimp [rate]
        have hn0 : (0 : ℝ) ≤ n := by positivity
        nlinarith [mul_nonneg (sub_nonneg.mpr hrate) hn0]

/-- A cold-only menu, including the trivial-comparator branch, already is a
contractive forward estimate. -/
noncomputable def growingColdOnly_exponentialForwardEstimate
    (error : ℕ → ℝ) {ρ : ℝ} (w₀ : ℕ)
    (D : ∀ w, ι w → ℕ → ℝ) (A α : ∀ w, ι w → ℝ)
    (hρ : 0 < ρ) (hρ8 : ρ ≤ 1 / 8) (hw₀ : 3 ≤ w₀)
    (hD : ∀ w i b, 0 ≤ D w i b) (hA : ∀ w i, 0 < A w i)
    (hgap : ∀ w i,
      α w i ≤ (halfDegree w : ℝ) / 4 - ρ * w / 4)
    (hmass : GrowingMenuMassBound w₀ D A)
    (hphysical : GrowingColdOnlyPhysicalBound error w₀ D A α) :
    ExponentialForwardEstimate error := by
  have hcold := growingMenuMass_cold_overhead w₀ D A hρ hw₀ hD hA hmass
  have hratio := eventually_growing_ratio_half hρ
  have hall : ∀ᶠ n : ℕ in atTop,
      error n ≤ ∑ b ∈ Finset.range n,
        growingQuotientColdRow w₀ D A α n b * ordinarySubgroupRatio b ∧
      (∀ w, w ∈ Finset.Ico w₀ (n + 1) →
        eulerProduct⁻¹ ^ 2 * (((n + 1 : ℕ) : ℝ) ^ (w + 2)) *
            (2 : ℝ) ^ ((halfDegree w : ℝ) / 4 + 1 / 4) *
            (∑ i, D w i (n - w) / A w i) ≤
          (2 : ℝ) ^ (ρ * w * n / 16)) ∧
      (2 : ℝ) ^ (-ρ * n / 8) ≤ 1 / 2 := by
    filter_upwards [hphysical, hcold, hratio] with n hp hc hr
    exact ⟨hp, hc, hr⟩
  let witness := eventually_atTop.mp hall
  let N : ℕ := Classical.choose witness
  have hN := Classical.choose_spec witness
  let rate : ℝ := ρ * w₀ / 8
  refine
    { scalar := fun _ => 0
      kernel := growingQuotientColdRow w₀ D A α
      threshold := N
      rate := rate
      scalarConst := 1
      rowConst := 2
      rate_pos := by dsimp [rate]; positivity
      scalarConst_pos := by norm_num
      rowConst_nonneg := by norm_num
      kernel_nonneg := ?_
      recurrence := ?_
      scalar_decay := ?_
      row_decay := ?_ }
  · intro n _ b _
    exact growingQuotientColdRow_nonneg w₀ D A α hD hA n b
  · intro n hn
    simpa using (hN n hn).1
  · intro n _
    positivity
  · intro n hn
    obtain ⟨_, hcoldn, hration⟩ := hN n hn
    have hrow := growingQuotientColdRow_sum_le
      w₀ n D A α hρ hρ8 hw₀ hD hA hgap hcoldn hration
    dsimp [rate]
    convert hrow using 1
    ring_nf

end SymmetricSubgroupAsymptotics

end
