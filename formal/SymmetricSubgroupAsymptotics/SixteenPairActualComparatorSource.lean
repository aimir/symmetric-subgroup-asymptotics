import SymmetricSubgroupAsymptotics.BinaryPairCompleteMomentLift
import SymmetricSubgroupAsymptotics.PrimitiveTwelvePairActualSource
import SymmetricSubgroupAsymptotics.WidthThirtyTwoBinaryRankTailResidual
import SymmetricSubgroupAsymptotics.PermutationNormalAxisCardBound

/-! Universal actual sixteen-pair source. The SAME sixteen-point top
is the comparator; the actual binary kernel has uniform natural capacity
six. McIver--Neumann, already retained by T1, bounds the number of original
normal axes using their actual degree32 action. No sixteen-point locator,
primitivity, affine assumption, or new published input is used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.SixteenPairActualComparatorSource
open Non2UnipotentPrefixFiniteMenu PrimitiveSocleRawStructure
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

variable (p : PreE7PairActionClass 16)
    (F : BinaryPairFrame (preE7PairAction 16 p) (Fin 16))

    (hMN : McIverNeumannPermutationGeneratorBound)

/-- The proved refined input gives the actual sixteen-point natural module
six generators uniformly over all invariant subspaces. -/
theorem natural_uniform {G : Type} [Group G] [Finite G]
    [MulAction G (Fin 16)] [MulAction.IsPretransitive G (Fin 16)] :
    UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) G (Fin 16)) 6 := by
  obtain ⟨H,hb,hu⟩ := traceyRefinedInducedModuleInput_proved.permutation
    G (Fin 16) 0 (by simp)
  have hh := hb.primePower 2 4 Nat.prime_two (by decide) (by norm_num)
  have hH : H ≤ 6 := by
    norm_num at hh
    exact_mod_cast hh
  exact uniformSubrepresentationGeneratorBound_mono _ hu hH

include F in
private theorem original_order_le (ht : Nat.card F.top.range ≤ 2^45) :
    Nat.card (preE7PairAction 16 p) ≤ 2^61 := by
  have hk : Nat.card F.kernelSpace ≤ 2^16 := by
    have hh := Nat.card_le_card_of_injective
      (Subtype.val : F.kernelSpace → (Fin 16 → ZMod 2)) Subtype.val_injective
    have hf : Nat.card (Fin 16 → ZMod 2)=2^16 := by
      rw [Nat.card_fun,Nat.card_fin,Nat.card_eq_fintype_card (α := ZMod 2),ZMod.card]
    rwa [hf] at hh
  rw [←F.kernelSpace_card_mul_top]
  exact (Nat.mul_le_mul hk ht).trans_eq (by rw [←pow_add])

include hMN in
private theorem moment_bound (b : ℕ) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)),completeQuotientWeight (R := preE7PairAction 16 p) J) ≤
      BinaryKernelRankTailNumerics.raw ((2 : ℝ)^(976 : ℕ)) 35184372088893 b+
        ((2 : ℝ)^(3721 : ℕ)*(2 : ℝ)^((153/100 : ℝ)*b))*
          ∑ J : Subgroup (Equiv.Perm (Fin b)),completeQuotientWeight (R := F.top.range) J := by
  letI : MulAction.IsPretransitive F.top.range (Fin 16) := F.top_pretransitive
  have ht : Nat.card F.top.range ≤ 2^45 := by
    have hh := Nat.card_le_card_of_injective F.top.range.subtype Subtype.val_injective
    have hc : Nat.card (Equiv.Perm (Fin 16))=Nat.factorial 16 := by
      simp only [Nat.card_perm,Nat.card_fin]
    exact (hh.trans_eq hc).trans (by norm_num)
  have hU : Nat.card (preE7PairAction 16 p) ≤ 2^61 :=
    original_order_le p F ht
  have hN : (Nat.card {N : Subgroup (preE7PairAction 16 p) // N.Normal} : ℝ) ≤
      (2 : ℝ)^(976 : ℕ) := by
    exact_mod_cast permutation_normalSubgroup_card_le hMN (by decide) (preE7PairAction 16 p) 61 hU
  have hh := BinaryPairCompleteMomentLift.complete_moment_le F
    natural_uniform 61 45 hU ht b
  norm_num only [Nat.reduceMul,Nat.reducePow,Nat.reduceAdd,Nat.cast_ofNat] at hh
  apply hh.trans
  calc
    _ ≤ (2 : ℝ)^(976 : ℕ)*(BinaryKernelRankTailNumerics.raw 1 35184372088893 b+
        ((2 : ℝ)^(2745 : ℕ)*(2 : ℝ)^((153/100 : ℝ)*b))*
          ∑ J : Subgroup (Equiv.Perm (Fin b)),completeQuotientWeight (R := F.top.range) J) := by
      apply mul_le_mul_of_nonneg_right hN
      have hz : 0 ≤ ∑ J : Subgroup (Equiv.Perm (Fin b)),completeQuotientWeight (R := F.top.range) J :=
        Finset.sum_nonneg (fun J _ => completeQuotientWeight_nonneg J)
      have hraw : 0 ≤ BinaryKernelRankTailNumerics.raw 1 35184372088893 b := by
        unfold BinaryKernelRankTailNumerics.raw
        exact mul_nonneg
          (mul_nonneg zero_le_one (pow_nonneg (Nat.cast_nonneg _) _))
          (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Nat.cast_nonneg _))
      exact add_nonneg hraw
        (mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) _)
          (Real.rpow_nonneg (by norm_num) _)) hz)
    _ = _ := by
      unfold BinaryKernelRankTailNumerics.raw
      rw [show (3721 : ℕ)=976+2745 by decide,pow_add]
      ring

include hMN in
/-- A complete raw source for the SAME original32-point pair action. -/
def data : PreE7DegreeTwoPairSummedSource 32
    (preE7SmallPairNonPairAction 16 (by decide) p) where
  R := F.top.range
  v := 16
  action := F.top.range.subtype
  action_injective := Subtype.val_injective
  mainCoefficient := (2 : ℝ)^(3721 : ℕ)
  coldCoefficient := fun _ => 0
  eta := 153/100
  theta := 0
  mainCoefficient_nonneg := by positivity
  coldCoefficient_nonneg := fun _ => le_rfl
  exceptionalRaw := BinaryKernelRankTailNumerics.raw ((2 : ℝ)^(976 : ℕ)) 35184372088893
  exceptionalRaw_nonneg := by
    intro b
    unfold BinaryKernelRankTailNumerics.raw
    exact mul_nonneg
      (mul_nonneg (pow_nonneg (by norm_num) _) (pow_nonneg (Nat.cast_nonneg _) _))
      (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Nat.cast_nonneg _))
  summed := by
    intro b P
    have hphysical :
        (∑ J : Subgroup (Equiv.Perm (Fin b)),fusionCompleteSourceSum (preE7PairAction 16 p) P J) ≤
        ∑ J : Subgroup (Equiv.Perm (Fin b)),completeQuotientWeight (R := preE7PairAction 16 p) J := by
      apply Finset.sum_le_sum
      intro J _
      unfold fusionCompleteSourceSum completeQuotientWeight completeQuotientCount
      rw [Nat.cast_sum]
      exact Finset.sum_le_sum (fun N _ =>
        fusionSurvivingEpiCount_le_groupEpimorphism_card (preE7PairAction 16 p) P N J)
    apply hphysical.trans
    apply (moment_bound p F hMN b).trans_eq
    simp only [zero_mul,add_zero,←Finset.mul_sum]
    ring

/-- All entry parameters are literal rational inequalities. -/
private theorem parameters : PreE7CharacterEntryParameters preE7CharacterRho 32 16
    (153/100) (1/100) (401/200) (707/200) 0 := by
  constructor <;> norm_num [preE7CharacterRho,halfDegree]

/-- The existing width32 menu pays the fixed normal-axis and top-generator
coefficient; the actual comparator is not replaced by its order. -/
def numericalMargin : (data p F hMN).NumericalMargin where
  D := fun _ => (2 : ℝ)^(3721 : ℕ)
  combinedEta := 153/100
  delta := 1/100
  cutoff := 401/200
  alpha := 707/200
  alpha_eq := by norm_num
  D_nonneg := fun _ => by positivity
  width_upper := by decide
  parameters := parameters
  total_growth := by
    intro b
    have hh := WidthThirtyTwoBinaryRankTailResidual.two_rpow_fiveThousand_le_menuMass
      (w := 32) rfl b
    rw [Real.rpow_natCast] at hh
    exact (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by decide : 3721 ≤ 5000)).trans hh
  combined_summed := by
    intro b P
    exact (data p F hMN).summed b P
  exceptional := by
    intro hc
    have ha : (1 : ℝ) ≤ Nat.card (Subgroup.normalizer
        (preE7PairAction 16 p : Set (Equiv.Perm (Fin 32)))) := by
      exact_mod_cast Nat.succ_le_of_lt (Nat.card_pos (α := Subgroup.normalizer
        (preE7PairAction 16 p : Set (Equiv.Perm (Fin 32)))))
    have heq : (data p F hMN).exceptionalScalar =
        BinaryKernelRankTailNumerics.pointed 16
          (Nat.card (Subgroup.normalizer
            (preE7PairAction 16 p : Set (Equiv.Perm (Fin 32)))) : ℝ)
          ((2 : ℝ)^(976 : ℕ)) 35184372088893 := by
      funext b
      rfl
    rw [heq]
    exact BinaryKernelRankTailNumerics.exponentialBound hc 16 35184372088893
      (by decide) _ _ ha (by positivity)

include hMN in
/-- The only input is the McIver--Neumann bound already retained by T1;
no action classification or structural locator is a premise. -/
def source : PreE7RankTailSourceOrYonedaTopData 32
    (preE7SmallPairNonPairAction 16 (by decide) p) :=
  .inr (.inr ((data p F hMN).toResidualChoice (numericalMargin p F hMN)))

end SymmetricSubgroupAsymptotics.SixteenPairActualComparatorSource

namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
open PrimitiveAffineImprimitiveBlockTransfer
/-- Universal actual16-pair representative source, without published16. -/
def actualSixteenPairRepresentativeSource
    (hMN : McIverNeumannPermutationGeneratorBound) : DegreeTwoSixteenPairRepresentativeSource :=
  fun p => SixteenPairActualComparatorSource.source p (preE7PairFrame 16 p) hMN
end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
