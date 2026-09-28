import SymmetricSubgroupAsymptotics.RepeatedMarkerOwnerBound
import SymmetricSubgroupAsymptotics.OddMarkerCoefficientBounds
import SymmetricSubgroupAsymptotics.ElementaryBenchmarkEstimates

/-!
# Final closure of the ordinary frontier

The repeated-marker theorem leaves exactly an outside-`Fits` term, the
proved marker continuation row, and a parity-adjusted binary error term.
This file packages the two remaining physical estimates in their honest
ambient-degree form and proves that they imply `T1` and hence `AllTargets`.
No boundedness of the total subgroup count is assumed: the existing forward
recurrence theorem derives it from eventual contraction.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics.OrdinaryFrontierClosure

open RepeatedMarkerOwnerBound

/-- The remaining non-binary physical frontier, indexed by the original
degree rather than by its rank and parity separately. -/
def outsideFrontierRatio (n : ℕ) : ℝ :=
  outsideFitsRatio (halfDegree n) (parity n)

/-- The remaining binary frontier after the checked odd marker transfer. -/
def binaryFrontierRatio (n : ℕ) : ℝ :=
  if parity n = 0 then
    binaryErrorRatio (halfDegree n)
  else
    OddMarkerBinaryErrorTransfer.currentCoefficient (halfDegree n) *
        binaryErrorRatio (halfDegree n) +
      OddMarkerBinaryErrorTransfer.predecessorErrorCoefficient (halfDegree n) *
        binaryErrorRatio (halfDegree n - 1)

/-- A complete forward estimate in the exact format consumed by the final
ordinary-remainder recurrence.  The scalar need not be nonnegative. -/
structure ExponentialForwardEstimate (error : ℕ → ℝ) where
  scalar : ℕ → ℝ
  kernel : ℕ → ℕ → ℝ
  threshold : ℕ
  rate : ℝ
  scalarConst : ℝ
  rowConst : ℝ
  rate_pos : 0 < rate
  scalarConst_pos : 0 < scalarConst
  rowConst_nonneg : 0 ≤ rowConst
  kernel_nonneg :
    ∀ n, threshold ≤ n → ∀ m ∈ Finset.range n, 0 ≤ kernel n m
  recurrence :
    ∀ n, threshold ≤ n →
      error n ≤ scalar n +
        ∑ m ∈ Finset.range n, kernel n m * ordinarySubgroupRatio m
  scalar_decay :
    ∀ n, threshold ≤ n →
      scalar n ≤ scalarConst * (2 : ℝ) ^ (-rate * (n : ℝ))
  row_decay :
    ∀ n, threshold ≤ n →
      (∑ m ∈ Finset.range n, kernel n m) ≤
        rowConst * (2 : ℝ) ^ (-rate * (n : ℝ))

/-- The two parity-specific physical frontiers are exactly one ambient-degree
frontier.  The lower bound excludes only the isolated odd degree one case. -/
theorem ordinaryRemainderRatio_le_frontier (n : ℕ) (hn : 3 ≤ n) :
    ordinaryRemainderRatio n ≤
      outsideFrontierRatio n +
        (∑ m ∈ Finset.range n,
          MarkerDegreeForwardRow.kernel n m * ordinarySubgroupRatio m) +
        binaryFrontierRatio n := by
  rcases parity_cases n with heven | hodd
  · have hdegree : 2 * halfDegree n = n := by
      have h := MarkerDegreeForwardRow.degree_identity n
      rw [heven, Nat.add_zero] at h
      exact h
    have h := even_remainder_frontier (halfDegree n)
    simpa only [outsideFrontierRatio, binaryFrontierRatio, heven, if_pos,
      hdegree] using h
  · have hdegree : 2 * halfDegree n + 1 = n := by
      have h := MarkerDegreeForwardRow.degree_identity n
      simpa only [hodd] using h
    have hhalf : 1 ≤ halfDegree n := by omega
    have h := odd_remainder_frontier (halfDegree n) hhalf
    simpa only [outsideFrontierRatio, binaryFrontierRatio, hodd,
      zero_ne_one, if_false, hdegree] using h

def finalScalar
    (O : ExponentialForwardEstimate outsideFrontierRatio)
    (B : ExponentialForwardEstimate binaryFrontierRatio) (n : ℕ) : ℝ :=
  O.scalar n + B.scalar n

def finalKernel
    (O : ExponentialForwardEstimate outsideFrontierRatio)
    (B : ExponentialForwardEstimate binaryFrontierRatio) (n m : ℕ) : ℝ :=
  MarkerDegreeForwardRow.kernel n m + O.kernel n m + B.kernel n m

/-- Two physical forward estimates close the whole counting target. -/
theorem T1_of_frontier_estimates
    (O : ExponentialForwardEstimate outsideFrontierRatio)
    (B : ExponentialForwardEstimate binaryFrontierRatio) : T1 := by
  obtain ⟨NM, hmarker⟩ :=
    Filter.eventually_atTop.mp MarkerDegreeForwardRow.eventually_row_le
  let N0 : ℕ := max 3 (max O.threshold (max B.threshold NM))
  let c : ℝ := min (1 / 20) (min O.rate B.rate)
  let Cs : ℝ := O.scalarConst + B.scalarConst
  let Ck : ℝ :=
    (2 : ℝ) ^ (1 / 20 : ℝ) + O.rowConst + B.rowConst
  have hc : 0 < c := by
    dsimp [c]
    exact lt_min (by norm_num) (lt_min O.rate_pos B.rate_pos)
  have hCs : 0 < Cs := by
    dsimp [Cs]
    exact add_pos O.scalarConst_pos B.scalarConst_pos
  have hCk : 0 ≤ Ck := by
    dsimp [Ck]
    exact add_nonneg
      (add_nonneg (Real.rpow_nonneg (by norm_num) _) O.rowConst_nonneg)
      B.rowConst_nonneg
  apply T1_of_ordinaryRemainder_recurrence
    (scalar := finalScalar O B) (kernel := finalKernel O B)
    (N := N0) (c := c) (Cs := Cs) (Ck := Ck)
    hc hCs hCk
  · intro n hn m hm
    have hnO : O.threshold ≤ n := by dsimp [N0] at hn; omega
    have hnB : B.threshold ≤ n := by dsimp [N0] at hn; omega
    exact add_nonneg
      (add_nonneg (MarkerDegreeForwardRow.kernel_nonneg n m)
        (O.kernel_nonneg n hnO m hm))
      (B.kernel_nonneg n hnB m hm)
  · intro n hn
    have hn3 : 3 ≤ n := by dsimp [N0] at hn; omega
    have hnO : O.threshold ≤ n := by dsimp [N0] at hn; omega
    have hnB : B.threshold ≤ n := by dsimp [N0] at hn; omega
    have hf := ordinaryRemainderRatio_le_frontier n hn3
    have ho := O.recurrence n hnO
    have hb := B.recurrence n hnB
    have hsum :
        (∑ m ∈ Finset.range n,
          finalKernel O B n m * ordinarySubgroupRatio m) =
          (∑ m ∈ Finset.range n,
            MarkerDegreeForwardRow.kernel n m * ordinarySubgroupRatio m) +
          (∑ m ∈ Finset.range n,
            O.kernel n m * ordinarySubgroupRatio m) +
          (∑ m ∈ Finset.range n,
            B.kernel n m * ordinarySubgroupRatio m) := by
      simp only [finalKernel, add_mul, Finset.sum_add_distrib]
    rw [hsum]
    dsimp only [finalScalar]
    linarith
  · intro n hn
    have hnO : O.threshold ≤ n := by dsimp [N0] at hn; omega
    have hnB : B.threshold ≤ n := by dsimp [N0] at hn; omega
    have ho := O.scalar_decay n hnO
    have hb := B.scalar_decay n hnB
    have hcO : c ≤ O.rate :=
      (min_le_right (1 / 20 : ℝ) (min O.rate B.rate)).trans
        (min_le_left O.rate B.rate)
    have hcB : c ≤ B.rate :=
      (min_le_right (1 / 20 : ℝ) (min O.rate B.rate)).trans
        (min_le_right O.rate B.rate)
    have hpowO : (2 : ℝ) ^ (-O.rate * (n : ℝ)) ≤
        (2 : ℝ) ^ (-c * (n : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have hpowB : (2 : ℝ) ^ (-B.rate * (n : ℝ)) ≤
        (2 : ℝ) ^ (-c * (n : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    calc
      finalScalar O B n ≤
          O.scalarConst * (2 : ℝ) ^ (-O.rate * (n : ℝ)) +
          B.scalarConst * (2 : ℝ) ^ (-B.rate * (n : ℝ)) :=
        add_le_add ho hb
      _ ≤ O.scalarConst * (2 : ℝ) ^ (-c * (n : ℝ)) +
          B.scalarConst * (2 : ℝ) ^ (-c * (n : ℝ)) :=
        add_le_add
          (mul_le_mul_of_nonneg_left hpowO O.scalarConst_pos.le)
          (mul_le_mul_of_nonneg_left hpowB B.scalarConst_pos.le)
      _ = Cs * (2 : ℝ) ^ (-c * (n : ℝ)) := by dsimp [Cs]; ring
  · intro n hn
    have hnO : O.threshold ≤ n := by dsimp [N0] at hn; omega
    have hnB : B.threshold ≤ n := by dsimp [N0] at hn; omega
    have hnM : NM ≤ n := by dsimp [N0] at hn; omega
    have hm := hmarker n hnM
    have ho := O.row_decay n hnO
    have hb := B.row_decay n hnB
    have hcM : c ≤ (1 / 20 : ℝ) := min_le_left _ _
    have hcO : c ≤ O.rate :=
      (min_le_right (1 / 20 : ℝ) (min O.rate B.rate)).trans
        (min_le_left O.rate B.rate)
    have hcB : c ≤ B.rate :=
      (min_le_right (1 / 20 : ℝ) (min O.rate B.rate)).trans
        (min_le_right O.rate B.rate)
    have hpowM : (2 : ℝ) ^ (-(n : ℝ) / 20) ≤
        (2 : ℝ) ^ (-c * (n : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have hpowO : (2 : ℝ) ^ (-O.rate * (n : ℝ)) ≤
        (2 : ℝ) ^ (-c * (n : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have hpowB : (2 : ℝ) ^ (-B.rate * (n : ℝ)) ≤
        (2 : ℝ) ^ (-c * (n : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have hsum :
        (∑ m ∈ Finset.range n, finalKernel O B n m) =
          (∑ m ∈ Finset.range n, MarkerDegreeForwardRow.kernel n m) +
          (∑ m ∈ Finset.range n, O.kernel n m) +
          (∑ m ∈ Finset.range n, B.kernel n m) := by
      simp only [finalKernel, Finset.sum_add_distrib]
    rw [hsum]
    calc
      _ ≤ (2 : ℝ) ^ (1 / 20 : ℝ) *
              (2 : ℝ) ^ (-(n : ℝ) / 20) +
            O.rowConst * (2 : ℝ) ^ (-O.rate * (n : ℝ)) +
            B.rowConst * (2 : ℝ) ^ (-B.rate * (n : ℝ)) :=
        add_le_add (add_le_add hm ho) hb
      _ ≤ (2 : ℝ) ^ (1 / 20 : ℝ) *
              (2 : ℝ) ^ (-c * (n : ℝ)) +
            O.rowConst * (2 : ℝ) ^ (-c * (n : ℝ)) +
            B.rowConst * (2 : ℝ) ^ (-c * (n : ℝ)) :=
        add_le_add
          (add_le_add
            (mul_le_mul_of_nonneg_left hpowM (by positivity))
            (mul_le_mul_of_nonneg_left hpowO O.rowConst_nonneg))
          (mul_le_mul_of_nonneg_left hpowB B.rowConst_nonneg)
      _ = Ck * (2 : ℝ) ^ (-c * (n : ℝ)) := by dsimp [Ck]; ring

/-- The already proved analytic transfers make the full approved theorem
package equivalent to closing the two physical frontier estimates. -/
theorem allTargets_of_frontier_estimates
    (O : ExponentialForwardEstimate outsideFrontierRatio)
    (B : ExponentialForwardEstimate binaryFrontierRatio) : AllTargets :=
  allTargets_iff_T1.mpr (T1_of_frontier_estimates O B)

end SymmetricSubgroupAsymptotics.OrdinaryFrontierClosure

end
