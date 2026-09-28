import SymmetricSubgroupAsymptotics.OrdinaryFrontierClosure

/-!
# Transport of a native binary recurrence to the final ambient frontier

Binary physical counting is naturally indexed by the half-degree `N` and
has forward targets below `2*N`.  The final ordinary recurrence is indexed
by the original degree and, in odd degree, contains the current and
predecessor binary errors with their exact marker coefficients.  This file
performs that transport once and for all.  The polynomial coefficient bounds
proved in `OddMarkerCoefficientBounds` preserve exponential decay.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics.BinaryFrontierTransport

open OddMarkerBinaryErrorTransfer OddMarkerCoefficientBounds
  OrdinaryFrontierClosure

/-- A native binary physical recurrence, before the odd marker transfer. -/
structure RankForwardEstimate where
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
    ∀ N, threshold ≤ N → ∀ m ∈ Finset.range (2 * N), 0 ≤ kernel N m
  recurrence :
    ∀ N, threshold ≤ N →
      binaryErrorRatio N ≤ scalar N +
        ∑ m ∈ Finset.range (2 * N), kernel N m * ordinarySubgroupRatio m
  scalar_decay :
    ∀ N, threshold ≤ N →
      scalar N ≤ scalarConst * (2 : ℝ) ^ (-rate * (N : ℝ))
  row_decay :
    ∀ N, threshold ≤ N →
      (∑ m ∈ Finset.range (2 * N), kernel N m) ≤
        rowConst * (2 : ℝ) ^ (-rate * (N : ℝ))

def paddedKernel (limit : ℕ) (k : ℕ → ℝ) (m : ℕ) : ℝ :=
  if m < limit then k m else 0

theorem paddedKernel_nonneg {limit : ℕ} {k : ℕ → ℝ}
    (hk : ∀ m ∈ Finset.range limit, 0 ≤ k m) (m : ℕ) :
    0 ≤ paddedKernel limit k m := by
  unfold paddedKernel
  split_ifs with hm
  · exact hk m (Finset.mem_range.mpr hm)
  · exact le_rfl

theorem paddedKernel_sum_mul_eq {limit n : ℕ} (hlimit : limit ≤ n)
    (k : ℕ → ℝ) (a : ℕ → ℝ) :
    (∑ m ∈ Finset.range n, paddedKernel limit k m * a m) =
      ∑ m ∈ Finset.range limit, k m * a m := by
  calc
    (∑ m ∈ Finset.range n, paddedKernel limit k m * a m) =
        ∑ m ∈ Finset.range limit, paddedKernel limit k m * a m := by
      symm
      apply Finset.sum_subset (Finset.range_mono hlimit)
      intro m hm hnot
      have hge : limit ≤ m := by
        simpa only [Finset.mem_range, not_lt] using hnot
      simp only [paddedKernel, if_neg (not_lt.mpr hge), zero_mul]
    _ = ∑ m ∈ Finset.range limit, k m * a m := by
      apply Finset.sum_congr rfl
      intro m hm
      simp only [paddedKernel, if_pos (Finset.mem_range.mp hm)]

theorem paddedKernel_sum_eq {limit n : ℕ} (hlimit : limit ≤ n)
    (k : ℕ → ℝ) :
    (∑ m ∈ Finset.range n, paddedKernel limit k m) =
      ∑ m ∈ Finset.range limit, k m := by
  simpa only [mul_one] using paddedKernel_sum_mul_eq hlimit k (fun _ => 1)

def ambientScalar (B : RankForwardEstimate) (n : ℕ) : ℝ :=
  if parity n = 0 then B.scalar (halfDegree n)
  else
    currentCoefficient (halfDegree n) * B.scalar (halfDegree n) +
      predecessorErrorCoefficient (halfDegree n) *
        B.scalar (halfDegree n - 1)

def ambientKernel (B : RankForwardEstimate) (n m : ℕ) : ℝ :=
  if parity n = 0 then
    paddedKernel (2 * halfDegree n) (B.kernel (halfDegree n)) m
  else
    currentCoefficient (halfDegree n) *
        paddedKernel (2 * halfDegree n) (B.kernel (halfDegree n)) m +
      predecessorErrorCoefficient (halfDegree n) *
        paddedKernel (2 * (halfDegree n - 1))
          (B.kernel (halfDegree n - 1)) m

private theorem halfDegree_ge_of_degree_ge (R n : ℕ) (hn : 2 * R ≤ n) :
    R ≤ halfDegree n := by
  have hdegree := MarkerDegreeForwardRow.degree_identity n
  have hp := parity_lt_two n
  omega

theorem ambientKernel_nonneg (B : RankForwardEstimate) {R n : ℕ}
    (hR : max (B.threshold + 1) R ≤ halfDegree n) (m : ℕ) :
    0 ≤ ambientKernel B n m := by
  have hbase : B.threshold ≤ halfDegree n := by omega
  have hpred : B.threshold ≤ halfDegree n - 1 := by omega
  unfold ambientKernel
  split_ifs
  · exact paddedKernel_nonneg (B.kernel_nonneg _ hbase) m
  · exact add_nonneg
      (mul_nonneg (currentCoefficient_nonneg _)
        (paddedKernel_nonneg (B.kernel_nonneg _ hbase) m))
      (mul_nonneg (OddMarkerCoefficientBounds.predecessorErrorCoefficient_nonneg _)
        (paddedKernel_nonneg (B.kernel_nonneg _ hpred) m))

theorem binaryFrontier_recurrence (B : RankForwardEstimate) (n : ℕ)
    (hn : 2 * (B.threshold + 1) ≤ n) :
    binaryFrontierRatio n ≤ ambientScalar B n +
      ∑ m ∈ Finset.range n, ambientKernel B n m * ordinarySubgroupRatio m := by
  have hr : B.threshold + 1 ≤ halfDegree n :=
    halfDegree_ge_of_degree_ge (B.threshold + 1) n hn
  have hbase : B.threshold ≤ halfDegree n := by omega
  have hpred : B.threshold ≤ halfDegree n - 1 := by omega
  rcases parity_cases n with heven | hodd
  · have hdegree : 2 * halfDegree n = n := by
      have h := MarkerDegreeForwardRow.degree_identity n
      rw [heven, Nat.add_zero] at h
      exact h
    have hrec := B.recurrence (halfDegree n) hbase
    have hpad := paddedKernel_sum_mul_eq (show 2 * halfDegree n ≤ n by omega)
      (B.kernel (halfDegree n)) ordinarySubgroupRatio
    rw [← hpad] at hrec
    simpa only [binaryFrontierRatio, ambientScalar, ambientKernel, heven,
      if_pos, hdegree] using hrec
  · have hdegree : 2 * halfDegree n + 1 = n := by
      have h := MarkerDegreeForwardRow.degree_identity n
      simpa only [hodd] using h
    have hcur := B.recurrence (halfDegree n) hbase
    have hpre := B.recurrence (halfDegree n - 1) hpred
    have hpadCur := paddedKernel_sum_mul_eq
      (show 2 * halfDegree n ≤ n by omega)
      (B.kernel (halfDegree n)) ordinarySubgroupRatio
    have hpadPre := paddedKernel_sum_mul_eq
      (show 2 * (halfDegree n - 1) ≤ n by omega)
      (B.kernel (halfDegree n - 1)) ordinarySubgroupRatio
    rw [← hpadCur] at hcur
    rw [← hpadPre] at hpre
    have hcur' := mul_le_mul_of_nonneg_left hcur
      (currentCoefficient_nonneg (halfDegree n))
    have hpre' := mul_le_mul_of_nonneg_left hpre
      (OddMarkerCoefficientBounds.predecessorErrorCoefficient_nonneg (halfDegree n))
    calc
      binaryFrontierRatio n =
          currentCoefficient (halfDegree n) * binaryErrorRatio (halfDegree n) +
            predecessorErrorCoefficient (halfDegree n) *
              binaryErrorRatio (halfDegree n - 1) := by
        simp only [binaryFrontierRatio, hodd, one_ne_zero, if_false]
      _ ≤ currentCoefficient (halfDegree n) *
            (B.scalar (halfDegree n) +
              ∑ m ∈ Finset.range n,
                paddedKernel (2 * halfDegree n) (B.kernel (halfDegree n)) m *
                  ordinarySubgroupRatio m) +
          predecessorErrorCoefficient (halfDegree n) *
            (B.scalar (halfDegree n - 1) +
              ∑ m ∈ Finset.range n,
                paddedKernel (2 * (halfDegree n - 1))
                    (B.kernel (halfDegree n - 1)) m * ordinarySubgroupRatio m) :=
        add_le_add hcur' hpre'
      _ = ambientScalar B n +
          ∑ m ∈ Finset.range n,
            ambientKernel B n m * ordinarySubgroupRatio m := by
        simp only [ambientScalar, ambientKernel, hodd, one_ne_zero, if_false,
          add_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
        ring

private def transportFactor (B : RankForwardEstimate) : ℝ :=
  9 + 16 * eulerProduct⁻¹ ^ 2 * (2 : ℝ) ^ B.rate

private theorem transportFactor_pos (B : RankForwardEstimate) :
    0 < transportFactor B := by
  unfold transportFactor
  positivity

private theorem shifted_exponential (B : RankForwardEstimate) (N : ℕ)
    (hN : 1 ≤ N) :
    (2 : ℝ) ^ (-B.rate * (((N - 1 : ℕ) : ℝ))) =
      (2 : ℝ) ^ B.rate * (2 : ℝ) ^ (-B.rate * (N : ℝ)) := by
  have hcast : (((N - 1 : ℕ) : ℝ)) = (N : ℝ) - 1 := by
    rw [Nat.cast_sub hN]
    norm_num
  rw [hcast, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  congr 1
  ring

private theorem rank_decay_le_degree_decay (B : RankForwardEstimate)
    (n : ℕ) (hr : 1 ≤ halfDegree n) :
    (2 : ℝ) ^ (-(B.rate / 2) * (halfDegree n : ℝ)) ≤
      (2 : ℝ) ^ (-(B.rate / 8) * (n : ℝ)) := by
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have hdegree := MarkerDegreeForwardRow.degree_identity n
  have hp := parity_lt_two n
  have hrate := B.rate_pos
  have hcast : (n : ℝ) ≤ 2 * (halfDegree n : ℝ) + 1 := by
    exact_mod_cast (show n ≤ 2 * halfDegree n + 1 by omega)
  have hrR : (1 : ℝ) ≤ halfDegree n := by exact_mod_cast hr
  nlinarith

/-- Every native rank recurrence yields the exact parity-adjusted ambient
certificate consumed by `OrdinaryFrontierClosure`. -/
def toAmbientEstimate (B : RankForwardEstimate) :
    ExponentialForwardEstimate binaryFrontierRatio := by
  let currentWitness := Filter.eventually_atTop.mp
    (eventually_currentCoefficient_mul_exponential_le B.rate_pos)
  let predecessorWitness := Filter.eventually_atTop.mp
    (eventually_predecessorErrorCoefficient_mul_exponential_le B.rate_pos)
  let NC : ℕ := Classical.choose currentWitness
  let NP : ℕ := Classical.choose predecessorWitness
  have hcurrent := Classical.choose_spec currentWitness
  have hpredecessor := Classical.choose_spec predecessorWitness
  let R0 : ℕ := max (B.threshold + 1) (max NC NP)
  let N0 : ℕ := 2 * R0
  refine
    { scalar := ambientScalar B
      kernel := ambientKernel B
      threshold := N0
      rate := B.rate / 8
      scalarConst := transportFactor B * B.scalarConst
      rowConst := transportFactor B * B.rowConst
      rate_pos := div_pos B.rate_pos (by norm_num)
      scalarConst_pos := mul_pos (transportFactor_pos B) B.scalarConst_pos
      rowConst_nonneg := mul_nonneg (transportFactor_pos B).le B.rowConst_nonneg
      kernel_nonneg := ?_
      recurrence := ?_
      scalar_decay := ?_
      row_decay := ?_ }
  · intro n hn m hm
    have hR0 : R0 ≤ halfDegree n := by
      apply halfDegree_ge_of_degree_ge R0 n
      simpa only [N0] using hn
    exact ambientKernel_nonneg B (R := max NC NP)
      (by dsimp [R0] at hR0 ⊢; omega) m
  · intro n hn
    apply binaryFrontier_recurrence B n
    have hR0 : B.threshold + 1 ≤ R0 := by dsimp [R0]; omega
    have : 2 * R0 ≤ n := by simpa only [N0] using hn
    omega
  · intro n hn
    have hR0 : R0 ≤ halfDegree n := by
      apply halfDegree_ge_of_degree_ge R0 n
      simpa only [N0] using hn
    have hbase : B.threshold ≤ halfDegree n := by dsimp [R0] at hR0; omega
    have hpred : B.threshold ≤ halfDegree n - 1 := by dsimp [R0] at hR0; omega
    have hcurOn : NC ≤ halfDegree n := by dsimp [R0] at hR0; omega
    have hpreOn : NP ≤ halfDegree n := by dsimp [R0] at hR0; omega
    have hr1 : 1 ≤ halfDegree n := by dsimp [R0] at hR0; omega
    have hdegree := rank_decay_le_degree_decay B n hr1
    rcases parity_cases n with heven | hodd
    · have hs := B.scalar_decay (halfDegree n) hbase
      have hrateHalf :
          (2 : ℝ) ^ (-B.rate * (halfDegree n : ℝ)) ≤
            (2 : ℝ) ^ (-(B.rate / 2) * (halfDegree n : ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        nlinarith [B.rate_pos, Nat.cast_nonneg (α := ℝ) (halfDegree n)]
      calc
        ambientScalar B n = B.scalar (halfDegree n) := by
          simp only [ambientScalar, heven, if_pos]
        _ ≤ B.scalarConst * (2 : ℝ) ^ (-B.rate * (halfDegree n : ℝ)) := hs
        _ ≤ B.scalarConst * (2 : ℝ) ^ (-(B.rate / 2) * (halfDegree n : ℝ)) :=
          mul_le_mul_of_nonneg_left hrateHalf B.scalarConst_pos.le
        _ ≤ B.scalarConst * (2 : ℝ) ^ (-(B.rate / 8) * (n : ℝ)) :=
          mul_le_mul_of_nonneg_left hdegree B.scalarConst_pos.le
        _ ≤ transportFactor B * B.scalarConst *
            (2 : ℝ) ^ (-(B.rate / 8) * (n : ℝ)) := by
          have hfac : 1 ≤ transportFactor B := by
            unfold transportFactor
            have hnonneg : 0 ≤ 16 * eulerProduct⁻¹ ^ 2 *
                (2 : ℝ) ^ B.rate := by positivity
            linarith
          have hconst : B.scalarConst ≤ transportFactor B * B.scalarConst := by
            nlinarith [B.scalarConst_pos]
          exact mul_le_mul_of_nonneg_right hconst (by positivity)
    · have hsCur := B.scalar_decay (halfDegree n) hbase
      have hsPre := B.scalar_decay (halfDegree n - 1) hpred
      have hcurMul := mul_le_mul_of_nonneg_left hsCur
        (currentCoefficient_nonneg (halfDegree n))
      have hpreMul := mul_le_mul_of_nonneg_left hsPre
        (OddMarkerCoefficientBounds.predecessorErrorCoefficient_nonneg (halfDegree n))
      have hcAbs := hcurrent (halfDegree n) hcurOn
      have hpAbs := hpredecessor (halfDegree n) hpreOn
      have hshift := shifted_exponential B (halfDegree n) hr1
      have hcurBound : currentCoefficient (halfDegree n) * B.scalar (halfDegree n) ≤
          (8 * B.scalarConst) *
            (2 : ℝ) ^ (-(B.rate / 2) * (halfDegree n : ℝ)) := by
        calc
          _ ≤ currentCoefficient (halfDegree n) *
              (B.scalarConst * (2 : ℝ) ^ (-B.rate * (halfDegree n : ℝ))) := hcurMul
          _ = B.scalarConst *
              (currentCoefficient (halfDegree n) *
                (2 : ℝ) ^ (-B.rate * (halfDegree n : ℝ))) := by ring
          _ ≤ B.scalarConst *
              (8 * (2 : ℝ) ^ (-(B.rate / 2) * (halfDegree n : ℝ))) :=
            mul_le_mul_of_nonneg_left hcAbs B.scalarConst_pos.le
          _ = _ := by ring
      have hpreBound :
          predecessorErrorCoefficient (halfDegree n) *
              B.scalar (halfDegree n - 1) ≤
            (16 * eulerProduct⁻¹ ^ 2 * (2 : ℝ) ^ B.rate * B.scalarConst) *
              (2 : ℝ) ^ (-(B.rate / 2) * (halfDegree n : ℝ)) := by
        calc
          _ ≤ predecessorErrorCoefficient (halfDegree n) *
              (B.scalarConst *
                (2 : ℝ) ^ (-B.rate * (((halfDegree n - 1 : ℕ) : ℝ)))) := hpreMul
          _ = (B.scalarConst * (2 : ℝ) ^ B.rate) *
              (predecessorErrorCoefficient (halfDegree n) *
                (2 : ℝ) ^ (-B.rate * (halfDegree n : ℝ))) := by
            rw [hshift]
            ring
          _ ≤ (B.scalarConst * (2 : ℝ) ^ B.rate) *
              ((16 * eulerProduct⁻¹ ^ 2) *
                (2 : ℝ) ^ (-(B.rate / 2) * (halfDegree n : ℝ))) :=
            mul_le_mul_of_nonneg_left hpAbs
              (mul_nonneg B.scalarConst_pos.le (by positivity))
          _ = _ := by ring
      calc
        ambientScalar B n =
            currentCoefficient (halfDegree n) * B.scalar (halfDegree n) +
              predecessorErrorCoefficient (halfDegree n) *
                B.scalar (halfDegree n - 1) := by
          simp only [ambientScalar, hodd, one_ne_zero, if_false]
        _ ≤ (8 * B.scalarConst +
              16 * eulerProduct⁻¹ ^ 2 * (2 : ℝ) ^ B.rate * B.scalarConst) *
              (2 : ℝ) ^ (-(B.rate / 2) * (halfDegree n : ℝ)) := by
          calc
            _ ≤ (8 * B.scalarConst) *
                (2 : ℝ) ^ (-(B.rate / 2) * (halfDegree n : ℝ)) +
              (16 * eulerProduct⁻¹ ^ 2 * (2 : ℝ) ^ B.rate * B.scalarConst) *
                (2 : ℝ) ^ (-(B.rate / 2) * (halfDegree n : ℝ)) :=
              add_le_add hcurBound hpreBound
            _ = _ := by ring
        _ ≤ (8 * B.scalarConst +
              16 * eulerProduct⁻¹ ^ 2 * (2 : ℝ) ^ B.rate * B.scalarConst) *
              (2 : ℝ) ^ (-(B.rate / 8) * (n : ℝ)) :=
          mul_le_mul_of_nonneg_left hdegree (add_nonneg
            (mul_nonneg (by norm_num) B.scalarConst_pos.le)
            (mul_nonneg (by positivity) B.scalarConst_pos.le))
        _ ≤ transportFactor B * B.scalarConst *
              (2 : ℝ) ^ (-(B.rate / 8) * (n : ℝ)) := by
          have hconst : 8 * B.scalarConst +
                16 * eulerProduct⁻¹ ^ 2 * (2 : ℝ) ^ B.rate * B.scalarConst ≤
              transportFactor B * B.scalarConst := by
            unfold transportFactor
            nlinarith [B.scalarConst_pos,
              mul_nonneg (by positivity : 0 ≤ 16 * eulerProduct⁻¹ ^ 2 *
                (2 : ℝ) ^ B.rate) B.scalarConst_pos.le]
          exact mul_le_mul_of_nonneg_right hconst (by positivity)
  · intro n hn
    have hR0 : R0 ≤ halfDegree n := by
      apply halfDegree_ge_of_degree_ge R0 n
      simpa only [N0] using hn
    have hbase : B.threshold ≤ halfDegree n := by dsimp [R0] at hR0; omega
    have hpred : B.threshold ≤ halfDegree n - 1 := by dsimp [R0] at hR0; omega
    have hcurOn : NC ≤ halfDegree n := by dsimp [R0] at hR0; omega
    have hpreOn : NP ≤ halfDegree n := by dsimp [R0] at hR0; omega
    have hr1 : 1 ≤ halfDegree n := by dsimp [R0] at hR0; omega
    have hdegree := rank_decay_le_degree_decay B n hr1
    rcases parity_cases n with heven | hodd
    · have hpad := paddedKernel_sum_eq
        (show 2 * halfDegree n ≤ n by
          have h := MarkerDegreeForwardRow.degree_identity n
          omega)
        (B.kernel (halfDegree n))
      have hrow := B.row_decay (halfDegree n) hbase
      have hrateHalf :
          (2 : ℝ) ^ (-B.rate * (halfDegree n : ℝ)) ≤
            (2 : ℝ) ^ (-(B.rate / 2) * (halfDegree n : ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        nlinarith [B.rate_pos, Nat.cast_nonneg (α := ℝ) (halfDegree n)]
      calc
        (∑ m ∈ Finset.range n, ambientKernel B n m) =
            ∑ m ∈ Finset.range (2 * halfDegree n), B.kernel (halfDegree n) m := by
          simp only [ambientKernel, heven, if_pos]
          exact hpad
        _ ≤ B.rowConst * (2 : ℝ) ^ (-B.rate * (halfDegree n : ℝ)) := hrow
        _ ≤ B.rowConst * (2 : ℝ) ^ (-(B.rate / 2) * (halfDegree n : ℝ)) :=
          mul_le_mul_of_nonneg_left hrateHalf B.rowConst_nonneg
        _ ≤ B.rowConst * (2 : ℝ) ^ (-(B.rate / 8) * (n : ℝ)) :=
          mul_le_mul_of_nonneg_left hdegree B.rowConst_nonneg
        _ ≤ transportFactor B * B.rowConst *
            (2 : ℝ) ^ (-(B.rate / 8) * (n : ℝ)) := by
          have hconst : B.rowConst ≤ transportFactor B * B.rowConst := by
            have hfac : 1 ≤ transportFactor B := by
              unfold transportFactor
              have hnonneg : 0 ≤ 16 * eulerProduct⁻¹ ^ 2 *
                  (2 : ℝ) ^ B.rate := by positivity
              linarith
            nlinarith [B.rowConst_nonneg]
          exact mul_le_mul_of_nonneg_right hconst (by positivity)
    · have hpadCur := paddedKernel_sum_eq
        (show 2 * halfDegree n ≤ n by
          have h := MarkerDegreeForwardRow.degree_identity n
          omega)
        (B.kernel (halfDegree n))
      have hpadPre := paddedKernel_sum_eq
        (show 2 * (halfDegree n - 1) ≤ n by
          have h := MarkerDegreeForwardRow.degree_identity n
          omega)
        (B.kernel (halfDegree n - 1))
      have hrowCur := B.row_decay (halfDegree n) hbase
      have hrowPre := B.row_decay (halfDegree n - 1) hpred
      have hcurMul := mul_le_mul_of_nonneg_left hrowCur
        (currentCoefficient_nonneg (halfDegree n))
      have hpreMul := mul_le_mul_of_nonneg_left hrowPre
        (OddMarkerCoefficientBounds.predecessorErrorCoefficient_nonneg (halfDegree n))
      have hcAbs := hcurrent (halfDegree n) hcurOn
      have hpAbs := hpredecessor (halfDegree n) hpreOn
      have hshift := shifted_exponential B (halfDegree n) hr1
      have hcurBound : currentCoefficient (halfDegree n) *
            (∑ m ∈ Finset.range (2 * halfDegree n), B.kernel (halfDegree n) m) ≤
          (8 * B.rowConst) *
            (2 : ℝ) ^ (-(B.rate / 2) * (halfDegree n : ℝ)) := by
        calc
          _ ≤ currentCoefficient (halfDegree n) *
              (B.rowConst * (2 : ℝ) ^ (-B.rate * (halfDegree n : ℝ))) := hcurMul
          _ = B.rowConst * (currentCoefficient (halfDegree n) *
              (2 : ℝ) ^ (-B.rate * (halfDegree n : ℝ))) := by ring
          _ ≤ B.rowConst * (8 *
              (2 : ℝ) ^ (-(B.rate / 2) * (halfDegree n : ℝ))) :=
            mul_le_mul_of_nonneg_left hcAbs B.rowConst_nonneg
          _ = _ := by ring
      have hpreBound : predecessorErrorCoefficient (halfDegree n) *
            (∑ m ∈ Finset.range (2 * (halfDegree n - 1)),
              B.kernel (halfDegree n - 1) m) ≤
          (16 * eulerProduct⁻¹ ^ 2 * (2 : ℝ) ^ B.rate * B.rowConst) *
            (2 : ℝ) ^ (-(B.rate / 2) * (halfDegree n : ℝ)) := by
        calc
          _ ≤ predecessorErrorCoefficient (halfDegree n) *
              (B.rowConst *
                (2 : ℝ) ^ (-B.rate * (((halfDegree n - 1 : ℕ) : ℝ)))) := hpreMul
          _ = (B.rowConst * (2 : ℝ) ^ B.rate) *
              (predecessorErrorCoefficient (halfDegree n) *
                (2 : ℝ) ^ (-B.rate * (halfDegree n : ℝ))) := by
            rw [hshift]
            ring
          _ ≤ (B.rowConst * (2 : ℝ) ^ B.rate) *
              ((16 * eulerProduct⁻¹ ^ 2) *
                (2 : ℝ) ^ (-(B.rate / 2) * (halfDegree n : ℝ))) :=
            mul_le_mul_of_nonneg_left hpAbs
              (mul_nonneg B.rowConst_nonneg (by positivity))
          _ = _ := by ring
      calc
        (∑ m ∈ Finset.range n, ambientKernel B n m) =
            currentCoefficient (halfDegree n) *
                (∑ m ∈ Finset.range (2 * halfDegree n), B.kernel (halfDegree n) m) +
              predecessorErrorCoefficient (halfDegree n) *
                (∑ m ∈ Finset.range (2 * (halfDegree n - 1)),
                  B.kernel (halfDegree n - 1) m) := by
          simp only [ambientKernel, hodd, one_ne_zero, if_false,
            Finset.sum_add_distrib, ← Finset.mul_sum]
          rw [hpadCur, hpadPre]
        _ ≤ (8 * B.rowConst +
              16 * eulerProduct⁻¹ ^ 2 * (2 : ℝ) ^ B.rate * B.rowConst) *
              (2 : ℝ) ^ (-(B.rate / 2) * (halfDegree n : ℝ)) := by
          calc
            _ ≤ (8 * B.rowConst) *
                (2 : ℝ) ^ (-(B.rate / 2) * (halfDegree n : ℝ)) +
              (16 * eulerProduct⁻¹ ^ 2 * (2 : ℝ) ^ B.rate * B.rowConst) *
                (2 : ℝ) ^ (-(B.rate / 2) * (halfDegree n : ℝ)) :=
              add_le_add hcurBound hpreBound
            _ = _ := by ring
        _ ≤ (8 * B.rowConst +
              16 * eulerProduct⁻¹ ^ 2 * (2 : ℝ) ^ B.rate * B.rowConst) *
              (2 : ℝ) ^ (-(B.rate / 8) * (n : ℝ)) :=
          mul_le_mul_of_nonneg_left hdegree (add_nonneg
            (mul_nonneg (by norm_num) B.rowConst_nonneg)
            (mul_nonneg (by positivity) B.rowConst_nonneg))
        _ ≤ transportFactor B * B.rowConst *
              (2 : ℝ) ^ (-(B.rate / 8) * (n : ℝ)) := by
          have hconst : 8 * B.rowConst +
                16 * eulerProduct⁻¹ ^ 2 * (2 : ℝ) ^ B.rate * B.rowConst ≤
              transportFactor B * B.rowConst := by
            unfold transportFactor
            nlinarith [B.rowConst_nonneg,
              mul_nonneg (by positivity : 0 ≤ 16 * eulerProduct⁻¹ ^ 2 *
                (2 : ℝ) ^ B.rate) B.rowConst_nonneg]
          exact mul_le_mul_of_nonneg_right hconst (by positivity)

end SymmetricSubgroupAsymptotics.BinaryFrontierTransport

end
