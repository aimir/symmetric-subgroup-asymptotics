import SymmetricSubgroupAsymptotics.Non2PreE7B6RankTailInstance
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairSummedSource
import SymmetricSubgroupAsymptotics.TrivialQuotientComparator
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairQuotientPackage

/-!
# Raw six-pair B6 envelope

The B6 theorem is already source-summed, but its original interface is
physical.  Taking the survival predicate to be true recovers the literal
complete quotient moment.  This file records that pre-padding form for the
degree-three affine prepend and for finite six-pair dispatch.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PreE7B6ActionCertificate

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  (S : PreE7B6SourceData w U)

def rawColdCoefficient (b : ℕ) : ℝ := S.constant * (1 + b)

def rawExceptional (b : ℕ) : ℝ :=
  (normalCount (preE7NonPairAction w U) : ℝ) *
    ((Nat.factorial b : ℕ) : ℝ) ^ 16 *
      ((2 : ℝ) ^
          (-((b6RankTailExponent b : ℝ) * (13 / 50) * b)) *
        (subgroupCount (b + 2 * b6RankTailExponent b) : ℝ))

theorem rawColdCoefficient_nonneg (b : ℕ) :
    0 ≤ rawColdCoefficient S b := by
  unfold rawColdCoefficient
  exact mul_nonneg S.constant_nonneg (by positivity)

theorem rawExceptional_nonneg (b : ℕ) :
    0 ≤ rawExceptional (w := w) (U := U) b := by
  unfold rawExceptional
  positivity

/-- With the survival predicate true, the B6 complete source is exactly the
literal complete quotient weight. -/
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

/-- The literal six-pair quotient moment, with the cold row and correlated
binary-rank exceptional term still separated. -/
noncomputable def quotientSummedEnvelope
    (lit : PreE7CharacterLiterature) :
    PreE7DegreeTwoPairQuotientSummedEnvelope
      (preE7NonPairAction w U) where
  R := PUnit
  mainCoefficient := 0
  coldCoefficient := rawColdCoefficient S
  eta := 0
  theta := 4 / 3
  mainCoefficient_nonneg := le_rfl
  coldCoefficient_nonneg := rawColdCoefficient_nonneg S
  exceptionalRaw := rawExceptional (w := w) (U := U)
  exceptionalRaw_nonneg := rawExceptional_nonneg (w := w) (U := U)
  summed := fun b => by
    have h := S.summedSource_le lit b (b6RankTailExponent b)
      (fun _ => True)
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

/-- The B6 raw row has trivial complete-moment comparator.  Retain its
faithful empty action explicitly so another affine layer can prepend the row
without reconstructing hidden comparator data. -/
noncomputable def quotientSummedPackage
    (lit : PreE7CharacterLiterature) :
    PreE7DegreeTwoPairQuotientSummedPackage
      (preE7NonPairAction w U) := by
  let E := S.quotientSummedEnvelope lit
  letI : Subsingleton E.R := by
    change Subsingleton PUnit
    infer_instance
  exact
    { envelope := E
      v := 0
      action := 1
      action_injective := fun _ _ _ => Subsingleton.elim _ _ }

end PreE7B6ActionCertificate
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
