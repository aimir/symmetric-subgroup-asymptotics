import SymmetricSubgroupAsymptotics.BinaryCarrierWordBound
import SymmetricSubgroupAsymptotics.BinaryCarrierHistoryCons

/-! Exact expansion of the proved carrier-word bound into finite histories
of literal normal axes. Weights remain explicitly factored over the original
factors. The numerical rows are the actual group capacities and quotient
slopes; no row coverage, domination certificate or terminal attachment is
asserted by this module. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace BinaryCarrierWord

open FullSubdirectGoursat BinaryMarkedGoursatPeel BinaryCarrierHistoryEnergy

local instance historySubgroupFinite {G : Type*} [Group G] [Finite G] :
    Finite (Subgroup G) :=
  Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective

/-- Every normal at every actual factor is retained, including normals
with identical numerical rows. The empty history occurs exactly once. -/
def History : List Factor → Type
  | [] => PUnit.{1}
  | A :: w => NormalAxis A.Carrier × History w

instance historyFinite : (w : List Factor) → Finite (History w)
  | [] => inferInstanceAs (Finite PUnit.{1})
  | A :: w =>
      letI := historyFinite w
      inferInstanceAs (Finite (NormalAxis A.Carrier × History w))

attribute [local instance] Fintype.ofFinite

/-- Separate finite enumeration from the group-valued row expressions. -/
theorem sum_history_cons (A : Factor) (w : List Factor)
    (f : History (A :: w) → ℝ) :
    (∑ h : History (A :: w), f h) =
      ∑ N : NormalAxis A.Carrier, ∑ h : History w, f (N,h) := by
  have he := Fintype.sum_prod_type (fun h : NormalAxis A.Carrier × History w => f h)
  convert (config := { transparency := .reducible }) he
  exact eq_of_heq ‹_›

def historyWeight : (w : List Factor) → AxisWeights w → History w → ℝ
  | [], _, _ => 1
  | _ :: w, v, h => v.1 h.1 * historyWeight w v.2 h.2

def historyCost : (w : List Factor) → History w → ℝ → ℝ → ℝ → ℝ
  | [], _, _, _, _ => 0
  | _ :: w, h, x, y, z => cost h.1 x y z +
      historyCost w h.2 (x+(centerSlope h.1 : ℝ)) (y+(derivedSlope h.1 : ℝ)) z

/-- The literal group-theoretic row, with no numerical majorization. -/
def actualRow {A : Factor} (N : NormalAxis A.Carrier) : JointCapacityRow where
  k := head N
  n := orderLog N
  m := derivedHead N
  a₂ := radicalHead N
  c := (centerSlope N : ℝ)
  g := (derivedSlope N : ℝ)

@[simp] theorem actualRow_cost {A : Factor} (N : NormalAxis A.Carrier)
    (x y z : ℝ) : (actualRow N).cost x y z = cost N x y z := rfl

@[simp] theorem actualRow_c {A : Factor} (N : NormalAxis A.Carrier) :
    (actualRow N).c = (centerSlope N : ℝ) := rfl

@[simp] theorem actualRow_g {A : Factor} (N : NormalAxis A.Carrier) :
    (actualRow N).g = (derivedSlope N : ℝ) := rfl

/-- Rows are indexed by the original occurrence order, not by isomorphism
classes or by a set that would identify repeated factors. -/
def rows : {w : List Factor} → History w → Fin w.length → JointCapacityRow
  | [], _ => Fin.elim0
  | _ :: _, h => Fin.cases (actualRow h.1) (rows h.2)

@[simp] theorem rows_cons_zero (A : Factor) (w : List Factor)
    (h : History (A :: w)) : rows h 0 = actualRow h.1 := rfl

@[simp] theorem rows_cons_succ (A : Factor) (w : List Factor)
    (h : History (A :: w)) (i : Fin w.length) : rows h i.succ = rows h.2 i := rfl

theorem historyWeight_nonneg (w : List Factor) (v : AxisWeights w)
    (hv : WeightsNonnegative w v) (h : History w) : 0 ≤ historyWeight w v h := by
  induction w with
  | nil => exact zero_le_one
  | cons A w ih => exact mul_nonneg (hv.1 h.1) (ih v.2 hv.2 h.2)

/-- The sum on each original factor includes every literal normal axis. -/
def axisWeightSums : (w : List Factor) → AxisWeights w → Fin w.length → ℝ
  | [], _ => Fin.elim0
  | A :: w, v => Fin.cases (∑ N : NormalAxis A.Carrier, v.1 N) (axisWeightSums w v.2)

def axisWeightProduct : (w : List Factor) → AxisWeights w → ℝ
  | [], _ => 1
  | A :: w, v => (∑ N : NormalAxis A.Carrier, v.1 N) * axisWeightProduct w v.2

theorem axisWeightSums_nonneg (w : List Factor) (v : AxisWeights w)
    (hv : WeightsNonnegative w v) (i : Fin w.length) : 0 ≤ axisWeightSums w v i := by
  induction w with
  | nil => exact Fin.elim0 i
  | cons A w ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · exact Finset.sum_nonneg (fun N _ => hv.1 N)
      · exact ih v.2 hv.2 j

/-- No nonnegativity is needed for this exact distributive identity. -/
theorem historyWeight_sum_eq_axisWeightProduct (w : List Factor) (v : AxisWeights w) :
    (∑ h : History w, historyWeight w v h) = axisWeightProduct w v := by
  induction w with
  | nil => simp [History,historyWeight,axisWeightProduct]
  | cons A w ih =>
      calc
        _ = ∑ N : NormalAxis A.Carrier, ∑ h : History w,
            v.1 N * historyWeight w v.2 h := sum_history_cons A w _
        _ = ∑ N : NormalAxis A.Carrier,
            v.1 N * (∑ h : History w, historyWeight w v.2 h) := by
          apply Finset.sum_congr rfl
          intro N _
          rw [Finset.mul_sum]
        _ = _ := by
          rw [ih v.2]
          exact (Finset.sum_mul _ _ _).symm

theorem axisWeightProduct_eq_prod (w : List Factor) (v : AxisWeights w) :
    axisWeightProduct w v = ∏ i : Fin w.length, axisWeightSums w v i := by
  induction w with
  | nil => simp [axisWeightProduct]
  | cons A w ih =>
      change axisWeightProduct (A :: w) v =
        ∏ i : Fin (w.length+1), axisWeightSums (A :: w) v i
      rw [Fin.prod_univ_succ (fun i : Fin (w.length+1) => axisWeightSums (A :: w) v i)]
      change (∑ N : NormalAxis A.Carrier, v.1 N) * axisWeightProduct w v.2 =
        (∑ N : NormalAxis A.Carrier, v.1 N) * ∏ i : Fin w.length, axisWeightSums w v.2 i
      rw [ih v.2]

theorem historyWeight_sum_eq_prod (w : List Factor) (v : AxisWeights w) :
    (∑ h : History w, historyWeight w v h) =
      ∏ i : Fin w.length, axisWeightSums w v i :=
  (historyWeight_sum_eq_axisWeightProduct w v).trans (axisWeightProduct_eq_prod w v)

theorem axisWeightProduct_nonneg (w : List Factor) (v : AxisWeights w)
    (hv : WeightsNonnegative w v) : 0 ≤ axisWeightProduct w v := by
  rw [← historyWeight_sum_eq_axisWeightProduct]
  exact Finset.sum_nonneg (fun h _ => historyWeight_nonneg w v hv h)

/-- Exact expansion of the previously proved recursive normal-history sum.
The actual weights and actual shifted costs occur together in each summand. -/
theorem normalHistorySum_eq_sum (w : List Factor) (v : AxisWeights w)
    (x y z : ℝ) :
    normalHistorySum w v x y z =
      ∑ h : History w, historyWeight w v h * (2 : ℝ)^(historyCost w h x y z) := by
  induction w generalizing x y with
  | nil => simp [normalHistorySum,History,historyWeight,historyCost]
  | cons A w ih =>
      calc
        _ = ∑ N : NormalAxis A.Carrier,
            v.1 N * (2 : ℝ)^(cost N x y z) *
              (∑ h : History w, historyWeight w v.2 h *
                (2 : ℝ)^(historyCost w h
                  (x+(centerSlope N : ℝ)) (y+(derivedSlope N : ℝ)) z)) := by
          apply Finset.sum_congr rfl
          intro N _
          rw [ih v.2]
        _ = ∑ N : NormalAxis A.Carrier, ∑ h : History w,
            historyWeight (A :: w) v (N,h) *
              (2 : ℝ)^(historyCost (A :: w) (N,h) x y z) := by
          apply Finset.sum_congr rfl
          intro N _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro h _
          change v.1 N * (2 : ℝ)^(cost N x y z) *
              (historyWeight w v.2 h * (2 : ℝ)^(historyCost w h
                (x+(centerSlope N : ℝ)) (y+(derivedSlope N : ℝ)) z)) =
            (v.1 N * historyWeight w v.2 h) *
              (2 : ℝ)^(cost N x y z + historyCost w h
                (x+(centerSlope N : ℝ)) (y+(derivedSlope N : ℝ)) z)
          rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2) (cost N x y z)
            (historyCost w h (x+(centerSlope N : ℝ)) (y+(derivedSlope N : ℝ)) z)]
          ring
        _ = _ := (sum_history_cons A w (fun h : History (A :: w) =>
          historyWeight (A :: w) v h * (2 : ℝ)^(historyCost (A :: w) h x y z))).symm

/-- The group-derived recursive cost is exactly the finite prefix-cost
expression used by the checked numerical history-energy theorem. -/
theorem historyCost_eq_finiteHistoryCost (w : List Factor) (h : History w)
    (x y z : ℝ) :
    historyCost w h x y z = finiteHistoryCost (rows h) x y z := by
  induction w generalizing x y with
  | nil => exact (finiteHistoryCost_nil (rows h) x y z).symm
  | cons A w ih =>
      rw [show rows h = Fin.cases (actualRow h.1) (rows h.2) from rfl,
        finiteHistoryCost_cases]
      change cost h.1 x y z +
          historyCost w h.2 (x+(centerSlope h.1 : ℝ)) (y+(derivedSlope h.1 : ℝ)) z =
        cost h.1 x y z +
          finiteHistoryCost (rows h.2)
            (x+(centerSlope h.1 : ℝ)) (y+(derivedSlope h.1 : ℝ)) z
      rw [ih h.2]

theorem normalHistorySum_eq_finiteHistoryCost_sum (w : List Factor)
    (v : AxisWeights w) (x y z : ℝ) :
    normalHistorySum w v x y z =
      ∑ h : History w, historyWeight w v h * (2 : ℝ)^(finiteHistoryCost (rows h) x y z) := by
  rw [normalHistorySum_eq_sum]
  apply Finset.sum_congr rfl
  intro h _
  rw [historyCost_eq_finiteHistoryCost]

end BinaryCarrierWord
end SymmetricSubgroupAsymptotics
