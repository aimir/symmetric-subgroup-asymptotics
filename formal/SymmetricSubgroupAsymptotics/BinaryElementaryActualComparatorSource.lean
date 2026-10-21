import SymmetricSubgroupAsymptotics.BinaryElementaryCompleteMomentLift
import SymmetricSubgroupAsymptotics.FiniteGroupPaddedGenerators
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairSummedSource

/-! A reusable original-kernel cold-rank source adapter. Actual group order
bounds supply only fixed coefficients; the complete comparator is the SAME
actual quotient. Every literal normal axis and every original fusion map
is retained before any numerical source transfer. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.BinaryElementaryActualComparatorSource
open Non2UnipotentPrefixFiniteMenu

variable {G B : Type} [Group G] [Finite G] [Group B] [Finite B]
    (pi : G →* B) (hpi : Function.Surjective pi)
    (A : Rep.{0} (ZMod 2) B) (E : OriginalKernelModuleChart pi A)
    {c : ℕ} (hu : UniformSubrepresentationGeneratorBound A.ρ.dual c)
    (m t : ℕ) (hG : Nat.card G ≤ 2^m) (hB : Nat.card B ≤ 2^t)

include pi hpi E hu hG hB in
/-- The actual complete moment, with all original normal multiplicities
absorbed by a fixed coefficient rather than discarded. -/
theorem moment_bound (b : ℕ) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)),completeQuotientWeight (R := G) J) ≤
      BinaryKernelRankTailNumerics.raw ((2 : ℝ)^(m*m)) (m+2^t) b+
        ((2 : ℝ)^(m*m+m*t)*(2 : ℝ)^(((51/200 : ℝ)*c)*b))*
          ∑ J : Subgroup (Equiv.Perm (Fin b)),completeQuotientWeight (R := B) J := by
  have hN : (Nat.card {N : Subgroup G // N.Normal} : ℝ) ≤ (2 : ℝ)^(m*m) := by
    exact_mod_cast normalSubgroup_card_le_two_pow_sq m hG
  have hh := BinaryElementaryCompleteMomentLift.complete_moment_le
    pi hpi A E hu m t hG hB b
  apply hh.trans
  calc
    _ ≤ (2 : ℝ)^(m*m)*(BinaryKernelRankTailNumerics.raw 1 (m+2^t) b+
        ((2 : ℝ)^(m*t)*(2 : ℝ)^(((51/200 : ℝ)*c)*b))*
          ∑ J : Subgroup (Equiv.Perm (Fin b)),completeQuotientWeight (R := B) J) := by
      apply mul_le_mul_of_nonneg_right hN
      have hz : 0 ≤ ∑ J : Subgroup (Equiv.Perm (Fin b)),completeQuotientWeight (R := B) J :=
        Finset.sum_nonneg (fun J _ => completeQuotientWeight_nonneg J)
      have hraw : 0 ≤ BinaryKernelRankTailNumerics.raw 1 (m+2^t) b := by
        unfold BinaryKernelRankTailNumerics.raw
        exact mul_nonneg
          (mul_nonneg zero_le_one (pow_nonneg (Nat.cast_nonneg _) _))
          (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Nat.cast_nonneg _))
      exact add_nonneg hraw
        (mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) _)
          (Real.rpow_nonneg (by norm_num) _)) hz)
    _ = _ := by
      unfold BinaryKernelRankTailNumerics.raw
      rw [pow_add]
      ring

include pi hpi E hu hG hB in
/-- Before physical pointing this is a full quotient envelope for the
original group itself, with no predicate or optimized normal-axis choice. -/
def envelope : PreE7DegreeTwoPairQuotientSummedEnvelope G where
  R := B
  mainCoefficient := (2 : ℝ)^(m*m+m*t)
  coldCoefficient := fun _ => 0
  eta := (51/200 : ℝ)*c
  theta := 0
  mainCoefficient_nonneg := pow_nonneg (by norm_num) _
  coldCoefficient_nonneg := fun _ => le_rfl
  exceptionalRaw := BinaryKernelRankTailNumerics.raw ((2 : ℝ)^(m*m)) (m+2^t)
  exceptionalRaw_nonneg := by
    intro b
    unfold BinaryKernelRankTailNumerics.raw
    exact mul_nonneg
      (mul_nonneg (pow_nonneg (by norm_num) _) (pow_nonneg (Nat.cast_nonneg _) _))
      (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Nat.cast_nonneg _))
  summed := by
    intro b
    apply (moment_bound pi hpi A E hu m t hG hB b).trans_eq
    simp only [zero_mul,add_zero,←Finset.mul_sum]
    ring

end BinaryElementaryActualComparatorSource

namespace BinaryElementaryActualComparatorSource
open Non2UnipotentPrefixFiniteMenu

variable {w : ℕ} {U : PreE7NonPairActionClass w}
    {B : Type} [Group B] [Finite B]
    (pi : preE7NonPairAction w U →* B) (hpi : Function.Surjective pi)
    (A : Rep.{0} (ZMod 2) B) (E : OriginalKernelModuleChart pi A)
    {c : ℕ} (hu : UniformSubrepresentationGeneratorBound A.ρ.dual c)
    (m t : ℕ) (hG : Nat.card (preE7NonPairAction w U) ≤ 2^m)
    (hB : Nat.card B ≤ 2^t)
    (v : ℕ) (action : B →* Equiv.Perm (Fin v))
    (hfaithful : Function.Injective action)

include pi hpi E hu hG hB in
/-- Every physical fusion predicate is bounded on its ORIGINAL action and
its ORIGINAL normal denominators by the same complete actual comparator. -/
def data : PreE7DegreeTwoPairSummedSource w U where
  R := B
  v := v
  action := action
  action_injective := hfaithful
  mainCoefficient := (2 : ℝ)^(m*m+m*t)
  coldCoefficient := fun _ => 0
  eta := (51/200 : ℝ)*c
  theta := 0
  mainCoefficient_nonneg := pow_nonneg (by norm_num) _
  coldCoefficient_nonneg := fun _ => le_rfl
  exceptionalRaw := BinaryKernelRankTailNumerics.raw ((2 : ℝ)^(m*m)) (m+2^t)
  exceptionalRaw_nonneg := (envelope pi hpi A E hu m t hG hB).exceptionalRaw_nonneg
  summed := by
    intro b P
    have hphysical :
        (∑ J : Subgroup (Equiv.Perm (Fin b)),fusionCompleteSourceSum (preE7NonPairAction w U) P J) ≤
        ∑ J : Subgroup (Equiv.Perm (Fin b)),completeQuotientWeight (R := preE7NonPairAction w U) J := by
      apply Finset.sum_le_sum
      intro J _
      unfold fusionCompleteSourceSum completeQuotientWeight completeQuotientCount
      rw [Nat.cast_sum]
      exact Finset.sum_le_sum (fun N _ =>
        fusionSurvivingEpiCount_le_groupEpimorphism_card (preE7NonPairAction w U) P N J)
    exact hphysical.trans ((envelope pi hpi A E hu m t hG hB).summed b)

end BinaryElementaryActualComparatorSource
end SymmetricSubgroupAsymptotics
