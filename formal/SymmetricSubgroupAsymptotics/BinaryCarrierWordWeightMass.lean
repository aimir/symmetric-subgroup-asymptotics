import SymmetricSubgroupAsymptotics.BinaryCarrierWordHistory
import SymmetricSubgroupAsymptotics.BinaryCarrierWordOrder

/-! Count literal normal axes by their underlying subsets, then bound the
total mass of a product of original axis weights. The supplied upper bound
on each physical weight remains explicit; no catalogue count or physical
normalization is inferred from the order of a carrier.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.BinaryCarrierWord

open FullSubdirectGoursat

/-- Forgetting normality and subgroup operations still distinguishes every
literal normal axis. No quotient by conjugacy or isomorphism is taken. -/
theorem normalAxis_set_injective (A : Type*) [Group A] :
    Function.Injective (fun N : NormalAxis A => (N.1 : Set A)) := by
  intro N L h
  exact Subtype.ext (SetLike.coe_injective h)

local instance weightMassNormalAxisFinite {A : Type*} [Group A] [Finite A] :
    Finite (NormalAxis A) :=
  Finite.of_injective (fun N : NormalAxis A => (N.1 : Set A))
    (normalAxis_set_injective A)

attribute [local instance] Fintype.ofFinite

/-- A finite group's actual normal axes form a subset of its power set.
This bound does not need the group to be a 2-group. -/
theorem normalAxis_card_le (A : Type*) [Group A] [Finite A] :
    Nat.card (NormalAxis A) ≤ 2 ^ Nat.card A := by
  have h := Nat.card_le_card_of_injective
    (fun N : NormalAxis A => (N.1 : Set A)) (normalAxis_set_injective A)
  have hset : Nat.card (Set A) = 2 ^ Nat.card A := by
    simpa only [Fintype.card_eq_nat_card] using (Fintype.card_set (α := A))
  exact h.trans_eq hset

/-- An explicit common upper bound for all original per-axis weights.
Nonnegativity is kept separately, as in the exact word-weight interface. -/
def WeightsLe : (w : List Factor) → AxisWeights w → ℝ → Prop
  | [], _, _ => True
  | _ :: w, v, M => (∀ N, v.1 N ≤ M) ∧ WeightsLe w v.2 M

/-- Bound one complete normal-axis sum without any finite enumeration. -/
theorem normalAxis_sum_le (A : Type*) [Group A] [Finite A]
    (v : NormalAxis A → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hv : ∀ N, v N ≤ M) :
    (∑ N : NormalAxis A, v N) ≤ M * (2 : ℝ) ^ Nat.card A := by
  have hcard : (Nat.card (NormalAxis A) : ℝ) ≤ (2 : ℝ) ^ Nat.card A := by
    exact_mod_cast normalAxis_card_le A
  calc
    _ ≤ ∑ _N : NormalAxis A, M := Finset.sum_le_sum (fun N _ => hv N)
    _ = (Nat.card (NormalAxis A) : ℝ) * M := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Fintype.card_eq_nat_card]
    _ ≤ ((2 : ℝ) ^ Nat.card A) * M := mul_le_mul_of_nonneg_right hcard hM
    _ = _ := mul_comm _ _

/-- The common original factor-order cap bounds every normal multiplicity.
The result retains the explicit upper bound M on actual weights. -/
theorem axisWeightProduct_le_of_orderBound
    (w : List Factor) (b : ℕ) (hb : OrderBound w b)
    (v : AxisWeights w) (hv : WeightsNonnegative w v)
    (M : ℝ) (hM : 0 ≤ M) (hle : WeightsLe w v M) :
    axisWeightProduct w v ≤ (M * (2 : ℝ) ^ (2^b : ℕ)) ^ w.length := by
  induction w with
  | nil => simp only [axisWeightProduct, List.length_nil, pow_zero, le_refl]
  | cons A w ih =>
      have hhead : (∑ N : NormalAxis A.Carrier, v.1 N) ≤
          M * (2 : ℝ) ^ (2^b : ℕ) :=
        (normalAxis_sum_le A.Carrier v.1 M hM hle.1).trans
          (mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hb.1) hM)
      have htail := ih hb.2 v.2 hv.2 hle.2
      have hbase : 0 ≤ M * (2 : ℝ) ^ (2^b : ℕ) :=
        mul_nonneg hM (pow_nonneg (by norm_num) _)
      change (∑ N : NormalAxis A.Carrier, v.1 N) * axisWeightProduct w v.2 ≤
        (M * (2 : ℝ) ^ (2^b : ℕ)) ^ (w.length+1)
      rw [pow_succ]
      exact (mul_le_mul hhead htail (axisWeightProduct_nonneg w v.2 hv.2) hbase).trans_eq
        (mul_comm _ _)

/-- The same bound applies to the exact sum of the original history
weights, including all repeated axes and the single empty history. -/
theorem historyWeight_sum_le_of_orderBound
    (w : List Factor) (b : ℕ) (hb : OrderBound w b)
    (v : AxisWeights w) (hv : WeightsNonnegative w v)
    (M : ℝ) (hM : 0 ≤ M) (hle : WeightsLe w v M) :
    (∑ h : History w, historyWeight w v h) ≤
      (M * (2 : ℝ) ^ (2^b : ℕ)) ^ w.length := by
  rw [historyWeight_sum_eq_axisWeightProduct]
  exact axisWeightProduct_le_of_orderBound w b hb v hv M hM hle

end SymmetricSubgroupAsymptotics.BinaryCarrierWord
