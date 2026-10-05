import SymmetricSubgroupAsymptotics.Non2PreE7Y1RankTailInstance
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairSummedSource
import SymmetricSubgroupAsymptotics.TrivialQuotientComparator

/-!
# The raw complete-quotient Y1 rank-tail envelope

The checked Y1 theorem was originally stated for the complete surviving
source attached to an arbitrary predicate.  Taking the predicate to be
true identifies that source with the literal complete quotient weight.
This file retains the resulting cold row and correlated hot term before
width-eight physical pointing, so a later affine layer may be prepended.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PreE7Y1ActionCertificate

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  (S : PreE7Y1SourceData w U)

def rawColdCoefficient (b : ℕ) : ℝ := S.constant * (1 + b)

def rawExceptional (b : ℕ) : ℝ :=
  (PreE7B6ActionCertificate.normalCount
      (preE7NonPairAction w U) : ℝ) *
    ((Nat.factorial b : ℕ) : ℝ) ^ 16 *
      ((Nat.factorial b : ℝ) *
        ((2 : ℝ) ^
            (-((rankTail51Tilt b : ℝ) * (51 / 200) * b)) *
          (subgroupCount (b + 2 * rankTail51Tilt b) : ℝ)))

theorem rawColdCoefficient_nonneg (b : ℕ) :
    0 ≤ rawColdCoefficient S b := by
  unfold rawColdCoefficient
  exact mul_nonneg S.constant_nonneg (by positivity)

theorem rawExceptional_nonneg (b : ℕ) :
    0 ≤ rawExceptional (w := w) (U := U) b := by
  unfold rawExceptional
  positivity

/-- With the predicate constantly true, every onto map survives, so the
complete-source sum is exactly the complete quotient weight. -/
theorem completeSource_true_eq_completeQuotientWeight (b : ℕ)
    (J : Subgroup (Equiv.Perm (Fin b))) :
    fusionCompleteSourceSum (preE7NonPairAction w U) (fun _ => True) J =
      completeQuotientWeight (R := preE7NonPairAction w U) J := by
  unfold fusionCompleteSourceSum fusionSurvivingEpiCount
    completeQuotientWeight completeQuotientCount
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro N _
  congr 1
  exact Nat.card_congr
    { toFun := fun beta => beta.1
      invFun := fun beta => ⟨beta, trivial⟩
      left_inv := fun beta => Subtype.ext rfl
      right_inv := fun _ => rfl }

/-- The exact source-summed package underlying the Y1 owner.  Its comparator
is the trivial group, whose complete quotient weight is one on every
source; hence the cold source count is the ordinary subgroup count. -/
noncomputable def quotientSummedEnvelope
    (lit : PreE7CharacterLiterature) :
    PreE7DegreeTwoPairQuotientSummedEnvelope
      (preE7NonPairAction w U) where
  R := PUnit
  mainCoefficient := 0
  coldCoefficient := rawColdCoefficient S
  eta := 0
  theta := 153 / 200
  mainCoefficient_nonneg := le_rfl
  coldCoefficient_nonneg := rawColdCoefficient_nonneg S
  exceptionalRaw := rawExceptional (w := w) (U := U)
  exceptionalRaw_nonneg := rawExceptional_nonneg (w := w) (U := U)
  summed := fun b => by
    have h := S.summedSource_le lit b (fun _ => True)
    have hleft :
        (∑ J : Subgroup (Equiv.Perm (Fin b)),
          completeQuotientWeight
            (R := preE7NonPairAction w U) J) =
        ∑ J : Subgroup (Equiv.Perm (Fin b)),
          fusionCompleteSourceSum
            (preE7NonPairAction w U) (fun _ => True) J := by
      apply Finset.sum_congr rfl
      intro J _
      exact (completeSource_true_eq_completeQuotientWeight
        (w := w) (U := U) b J).symm
    rw [hleft]
    apply h.trans_eq
    simp only [zero_mul, zero_add,
      completeQuotientWeight_eq_one_of_subsingleton,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Fintype.card_eq_nat_card, subgroupCount,
      rawColdCoefficient, rawExceptional]
    ring

end PreE7Y1ActionCertificate
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
