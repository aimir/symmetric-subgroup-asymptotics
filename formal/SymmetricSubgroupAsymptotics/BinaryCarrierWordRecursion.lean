import SymmetricSubgroupAsymptotics.BinaryCarrierWord
import SymmetricSubgroupAsymptotics.BinaryMarkedTailFamily

/-! A proved marked recurrence on full original carrier words. Each
successive axis belongs to the literal suffix image of the same subgroup.
Arbitrary original survival is retained on the left; only nonnegative
enlargements occur on the right. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace BinaryCarrierWord

open FullSubdirectGoursat BinaryMarkedGoursatPeel

attribute [local instance] Fintype.ofFinite

def firstAxis (A : Factor) (w : List Factor) (H : Family (A :: w)) :
    NormalAxis A.Carrier :=
  ⟨H.1.goursatFst,Subgroup.normal_goursatFst (first A w H).2⟩

/-- The first-step recurrence is proved for arbitrary weights depending on
the exact original tail and normal axis, before imposing product weights. -/
theorem weighted_step (A : Factor) (w : List Factor)
    (P : Subgroup (Product (A :: w)) → Prop)
    (v : Subgroup (Product w) → NormalAxis A.Carrier → ℝ)
    (hv : ∀ L, Full w L → ∀ N, 0 ≤ v L N)
    (x y z : ℝ) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    (∑ H : Family (A :: w), if P H.1 then
      v (tail A w H).1 (firstAxis A w H)*mark H.1 x y z else 0) ≤
      ∑ L : Family w, ∑ N : NormalAxis A.Carrier,
        v L.1 N * polynomial N L.1 * (2 : ℝ)^(cost N x y z) *
          mark L.1 (x+(centerSlope N : ℝ)) (y+(derivedSlope N : ℝ)) z := by
  have he :
      (∑ H : Family (A :: w), if P H.1 then
        v (tail A w H).1 (firstAxis A w H)*mark H.1 x y z else 0) =
      ∑ H : BinaryMarkedTailFamily.OriginalFamily A.Carrier (Product w) (Full w),
        if P H.1.1 then
          v (SubdirectTailImage.tail H.1.1)
            (BinaryMarkedTailFamily.originalAxis (Full w) H)*mark H.1.1 x y z else 0 := by
    apply Fintype.sum_equiv (familyPeelEquiv A w)
    intro H
    rfl
  rw [he]
  have h := BinaryMarkedTailFamily.weighted_peel_binary_ambient
    (A := A.Carrier) (B := Product w) (Full w) A.binary (product_binary w)
    P v hv x y z hy hz
  convert (config := { transparency := .reducible }) h

/-- A word weight contains one independent function on each actual factor's
normal subgroups. Dependence on intermediate tails is not silently factored. -/
def AxisWeights : List Factor → Type 1
  | [] => PUnit.{2}
  | A :: w => (NormalAxis A.Carrier → ℝ) × AxisWeights w

def WeightsNonnegative : (w : List Factor) → AxisWeights w → Prop
  | [], _ => True
  | _ :: w, v => (∀ N, 0 ≤ v.1 N) ∧ WeightsNonnegative w v.2

/-- Product weight along the canonical literal suffixes of the original H. -/
def weight : (w : List Factor) → AxisWeights w → Family w → ℝ
  | [], _, _ => 1
  | A :: w, v, H => v.1 (firstAxis A w H) * weight w v.2 (tail A w H)

theorem weight_nonneg (w : List Factor) (v : AxisWeights w)
    (hv : WeightsNonnegative w v) (H : Family w) : 0 ≤ weight w v H := by
  induction w with
  | nil => exact zero_le_one
  | cons A w ih => exact mul_nonneg (hv.1 _) (ih v.2 hv.2 (tail A w H))

/-- Extension to all literal subgroups is zero only outside the declared
full-coordinate family, so it supplies the exact fixed-tail weight. -/
def subgroupWeight (w : List Factor) (v : AxisWeights w)
    (H : Subgroup (Product w)) : ℝ :=
  if h : Full w H then weight w v ⟨H,h⟩ else 0

@[simp] theorem subgroupWeight_full (w : List Factor) (v : AxisWeights w)
    (H : Family w) : subgroupWeight w v H.1 = weight w v H := by
  simp only [subgroupWeight,dif_pos H.2]

theorem subgroupWeight_nonneg (w : List Factor) (v : AxisWeights w)
    (hv : WeightsNonnegative w v) (H : Subgroup (Product w)) :
    0 ≤ subgroupWeight w v H := by
  unfold subgroupWeight
  split_ifs with h
  · exact weight_nonneg w v hv ⟨H,h⟩
  · exact le_rfl

def markedSum (w : List Factor) (v : AxisWeights w)
    (P : Subgroup (Product w) → Prop) (x y z : ℝ) : ℝ :=
  ∑ H : Family w, if P H.1 then weight w v H * mark H.1 x y z else 0

theorem markedSum_nonneg (w : List Factor) (v : AxisWeights w)
    (hv : WeightsNonnegative w v) (P : Subgroup (Product w) → Prop)
    (x y z : ℝ) : 0 ≤ markedSum w v P x y z := by
  apply Finset.sum_nonneg
  intro H _
  split_ifs
  · exact mul_nonneg (weight_nonneg w v hv H) (mark_nonneg H.1 x y z)
  · exact le_rfl

/-- The actual full-word sum peels into the same marked literal tail sums.
Every axis and every tail still carries its original product weight. -/
theorem markedSum_cons_le (A : Factor) (w : List Factor)
    (v : AxisWeights (A :: w)) (hv : WeightsNonnegative (A :: w) v)
    (P : Subgroup (Product (A :: w)) → Prop)
    (x y z : ℝ) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    markedSum (A :: w) v P x y z ≤
      ∑ L : Family w, ∑ N : NormalAxis A.Carrier,
        v.1 N * weight w v.2 L * polynomial N L.1 * (2 : ℝ)^(cost N x y z) *
          mark L.1 (x+(centerSlope N : ℝ)) (y+(derivedSlope N : ℝ)) z := by
  let q (L : Subgroup (Product w)) (N : NormalAxis A.Carrier) :=
    v.1 N * subgroupWeight w v.2 L
  have hq (L : Subgroup (Product w)) (_ : Full w L) (N : NormalAxis A.Carrier) :
      0 ≤ q L N :=
    mul_nonneg (hv.1 N) (subgroupWeight_nonneg w v.2 hv.2 L)
  have h := weighted_step A w P q hq x y z hy hz
  have hleft :
      (∑ H : Family (A :: w), if P H.1 then
        q (tail A w H).1 (firstAxis A w H)*mark H.1 x y z else 0) =
      markedSum (A :: w) v P x y z := by
    apply Finset.sum_congr rfl
    intro H _
    simp only [q,subgroupWeight_full,weight]
  have hright :
      (∑ L : Family w, ∑ N : NormalAxis A.Carrier,
        q L.1 N * polynomial N L.1 * (2 : ℝ)^(cost N x y z) *
          mark L.1 (x+(centerSlope N : ℝ)) (y+(derivedSlope N : ℝ)) z) =
      ∑ L : Family w, ∑ N : NormalAxis A.Carrier,
        v.1 N * weight w v.2 L * polynomial N L.1 * (2 : ℝ)^(cost N x y z) *
          mark L.1 (x+(centerSlope N : ℝ)) (y+(derivedSlope N : ℝ)) z := by
    apply Finset.sum_congr rfl
    intro L _
    apply Finset.sum_congr rfl
    intro N _
    rw [show q L.1 N = v.1 N * subgroupWeight w v.2 L.1 from rfl,
      subgroupWeight_full]
  exact hleft ▸ hright ▸ h

end BinaryCarrierWord
end SymmetricSubgroupAsymptotics
