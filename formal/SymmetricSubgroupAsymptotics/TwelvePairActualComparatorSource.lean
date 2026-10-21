import SymmetricSubgroupAsymptotics.BinaryPairCompleteMomentLift
import SymmetricSubgroupAsymptotics.TwelvePairActualTopSource

/-! Universal actual twelve-pair source, retaining the top itself as a
faithful twelve-point comparator. The rank-tail cold price of the original
binary kernel is51/50, below the available width24 comparator margin5/4.
Every original normal axis and every hot-source map are retained. No
published twelve-point classification is used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.TwelvePairActualComparatorSource
open Non2UnipotentPrefixFiniteMenu PrimitiveSocleRawStructure
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

variable (p : PreE7PairActionClass 12)
    (F : BinaryPairFrame (preE7PairAction 12 p) (Fin 12))

private theorem moment_bound (b : ℕ) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)),completeQuotientWeight (R := preE7PairAction 12 p) J) ≤
      BinaryKernelRankTailNumerics.raw ((2 : ℝ)^(1681 : ℕ)) 536870953 b+
        ((2 : ℝ)^(2870 : ℕ)*(2 : ℝ)^((51/50 : ℝ)*b))*
          ∑ J : Subgroup (Equiv.Perm (Fin b)),completeQuotientWeight (R := F.top.range) J := by
  letI : MulAction.IsPretransitive F.top.range (Fin 12) := F.top_pretransitive
  have ht : Nat.card F.top.range ≤ 2^29 := degreeTwelve_group_order_le
  have hU : Nat.card (preE7PairAction 12 p) ≤ 2^41 :=
    TwelvePairActualKernelQuotientSum.original_order_le F ht
  have hN : (Nat.card {N : Subgroup (preE7PairAction 12 p) // N.Normal} : ℝ) ≤
      (2 : ℝ)^(1681 : ℕ) := by
    exact_mod_cast normalSubgroup_card_le_two_pow_sq 41 hU
  have hh := BinaryPairCompleteMomentLift.complete_moment_le F
    PrimitiveTwelvePairActualSource.natural_uniform 41 29 hU ht b
  norm_num only [Nat.reduceMul,Nat.reducePow,Nat.reduceAdd,Nat.cast_ofNat] at hh
  apply hh.trans
  calc
    _ ≤ (2 : ℝ)^(1681 : ℕ)*(BinaryKernelRankTailNumerics.raw 1 536870953 b+
        ((2 : ℝ)^(1189 : ℕ)*(2 : ℝ)^((51/50 : ℝ)*b))*
          ∑ J : Subgroup (Equiv.Perm (Fin b)),completeQuotientWeight (R := F.top.range) J) := by
      apply mul_le_mul_of_nonneg_right hN
      have hz : 0 ≤ ∑ J : Subgroup (Equiv.Perm (Fin b)),completeQuotientWeight (R := F.top.range) J :=
        Finset.sum_nonneg (fun J _ => completeQuotientWeight_nonneg J)
      have hraw : 0 ≤ BinaryKernelRankTailNumerics.raw 1 536870953 b := by
        unfold BinaryKernelRankTailNumerics.raw
        exact mul_nonneg
          (mul_nonneg zero_le_one (pow_nonneg (Nat.cast_nonneg _) _))
          (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Nat.cast_nonneg _))
      exact add_nonneg hraw
        (mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) _)
          (Real.rpow_nonneg (by norm_num) _)) hz)
    _ = _ := by
      unfold BinaryKernelRankTailNumerics.raw
      rw [show (2870 : ℕ)=1681+1189 by decide,pow_add]
      ring

/-- A complete raw source for the SAME original24-point pair action. -/
def data : PreE7DegreeTwoPairSummedSource 24
    (preE7SmallPairNonPairAction 12 (by decide) p) where
  R := F.top.range
  v := 12
  action := F.top.range.subtype
  action_injective := Subtype.val_injective
  mainCoefficient := (2 : ℝ)^(2870 : ℕ)
  coldCoefficient := fun _ => 0
  eta := 51/50
  theta := 0
  mainCoefficient_nonneg := by positivity
  coldCoefficient_nonneg := fun _ => le_rfl
  exceptionalRaw := BinaryKernelRankTailNumerics.raw ((2 : ℝ)^(1681 : ℕ)) 536870953
  exceptionalRaw_nonneg := by intro b; unfold BinaryKernelRankTailNumerics.raw; positivity
  summed := by
    intro b P
    have hphysical :
        (∑ J : Subgroup (Equiv.Perm (Fin b)),fusionCompleteSourceSum (preE7PairAction 12 p) P J) ≤
        ∑ J : Subgroup (Equiv.Perm (Fin b)),completeQuotientWeight (R := preE7PairAction 12 p) J := by
      apply Finset.sum_le_sum
      intro J _
      unfold fusionCompleteSourceSum completeQuotientWeight completeQuotientCount
      rw [Nat.cast_sum]
      exact Finset.sum_le_sum (fun N _ =>
        fusionSurvivingEpiCount_le_groupEpimorphism_card (preE7PairAction 12 p) P N J)
    apply hphysical.trans
    apply (moment_bound p F b).trans_eq
    simp only [zero_mul,add_zero,←Finset.mul_sum]
    ring

/-- All entry parameters are literal rational inequalities. -/
private theorem parameters : PreE7CharacterEntryParameters preE7CharacterRho 24 12
    (51/50) (1/100) (301/200) (101/40) 0 := by
  constructor <;> norm_num [preE7CharacterRho,halfDegree]

/-- The existing width24 menu pays the fixed normal-axis and top-generator
coefficient; the actual comparator is not replaced by its order. -/
def numericalMargin : (data p F).NumericalMargin where
  D := fun _ => (2 : ℝ)^(2870 : ℕ)
  combinedEta := 51/50
  delta := 1/100
  cutoff := 301/200
  alpha := 101/40
  alpha_eq := by norm_num
  D_nonneg := fun _ => by positivity
  width_upper := by decide
  parameters := parameters
  total_growth := by
    intro b
    have hh := WidthTwentyFourBinaryRankTailResidual.two_rpow_threeThousandSevenHundredFortyFour_le_menuMass
      (w := 24) rfl b
    rw [Real.rpow_natCast] at hh
    exact (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by decide : 2870 ≤ 3744)).trans hh
  combined_summed := by
    intro b P
    exact (data p F).summed b P
  exceptional := by
    intro hc
    have ha : (1 : ℝ) ≤ Nat.card (Subgroup.normalizer
        (preE7PairAction 12 p : Set (Equiv.Perm (Fin 24)))) := by
      exact_mod_cast Nat.succ_le_of_lt (Nat.card_pos (α := Subgroup.normalizer
        (preE7PairAction 12 p : Set (Equiv.Perm (Fin 24)))))
    have heq : (data p F).exceptionalScalar =
        BinaryKernelRankTailNumerics.pointed 12
          (Nat.card (Subgroup.normalizer
            (preE7PairAction 12 p : Set (Equiv.Perm (Fin 24)))) : ℝ)
          ((2 : ℝ)^(1681 : ℕ)) 536870953 := by
      funext b
      rfl
    rw [heq]
    exact BinaryKernelRankTailNumerics.exponentialBound hc 12 536870953
      (by decide) _ _ ha (by positivity)

/-- No classification, literature bound or structural locator is a premise
of this actual representative source. -/
def source : PreE7RankTailSourceOrYonedaTopData 24
    (preE7SmallPairNonPairAction 12 (by decide) p) :=
  .inr (.inr ((data p F).toResidualChoice (numericalMargin p F)))

end SymmetricSubgroupAsymptotics.TwelvePairActualComparatorSource
