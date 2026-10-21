import SymmetricSubgroupAsymptotics.TwelvePairActualKernelQuotientSum
import SymmetricSubgroupAsymptotics.WidthTwentyFourBinaryRankTailResidual
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairGeneralSourceAssembly

/-! Complete original-axis aggregation at width24. The geometric
constructors below consume proved bounds on the actual top and its natural
module; no finite catalogue completeness or source bound is a literature
assumption. Every original normal axis is retained. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.TwelvePairOriginalSource
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

variable (p : PreE7PairActionClass 12)
  (F : BinaryPairFrame (preE7PairAction 12 p) (Fin 12))
  (ht : Nat.card F.top.range≤2^29) (theta : ℝ)
  (hgap : theta≤(halfDegree 24 : ℝ)/4-preE7CharacterRho*24/4)
  (haxisSum : ∀ (N : Subgroup (preE7PairAction 12 p)) [N.Normal] (b : ℕ),
    (∑ J : Subgroup (Equiv.Perm (Fin b)),
      (Nat.card (GroupEpimorphism J (preE7PairAction 12 p ⧸ N)) : ℝ)) ≤
      BinaryKernelRankTailNumerics.raw 1 536870953 b+
        (subgroupCount b : ℝ)*((2 : ℝ)^(2030 : ℕ)*(2 : ℝ)^(theta*b)))

def data : WidthTwentyFourBinaryRankTailResidual.Data 24 (preE7SmallPairNonPairAction 12 (by decide) p) where
  cold := (2 : ℝ)^(3711 : ℕ)
  theta := theta
  hot := (2 : ℝ)^(1681 : ℕ)
  factorialPower := 536870953
  cold_nonneg := by positivity
  hot_nonneg := by positivity
  cold_le := pow_le_pow_right₀ (by norm_num : (1 : ℝ)≤2) (by decide : 3711≤3744)
  width := rfl
  tail_gap := hgap
  summed := by
    intro b P
    let G := preE7PairAction 12 p
    let Ax := {N : Subgroup G // N.Normal}
    have hU : Nat.card G≤2^41 :=
      TwelvePairActualKernelQuotientSum.original_order_le F ht
    have hn : (Nat.card Ax : ℝ)≤(2 : ℝ)^(1681 : ℕ) := by
      exact_mod_cast normalSubgroup_card_le_two_pow_sq 41 hU
    have hN (N : Ax) :
        (∑ J : Subgroup (Equiv.Perm (Fin b)),(Nat.card (GroupEpimorphism J (G ⧸ N.val)) : ℝ))≤
        BinaryKernelRankTailNumerics.raw 1 536870953 b+
          (subgroupCount b : ℝ)*((2 : ℝ)^(2030 : ℕ)*(2 : ℝ)^(theta*(b : ℝ))) :=
      haxisSum N.val b
    have hphysical :
        (∑ J : Subgroup (Equiv.Perm (Fin b)),fusionCompleteSourceSum G P J)≤
        ∑ J : Subgroup (Equiv.Perm (Fin b)),completeQuotientWeight (R := G) J := by
      apply Finset.sum_le_sum
      intro J _
      unfold fusionCompleteSourceSum completeQuotientWeight completeQuotientCount
      rw [Nat.cast_sum]
      exact Finset.sum_le_sum (fun N _ =>
        fusionSurvivingEpiCount_le_groupEpimorphism_card G P N J)
    have he :
        (∑ J : Subgroup (Equiv.Perm (Fin b)),completeQuotientWeight (R := G) J)=
        ∑ N : Ax,∑ J : Subgroup (Equiv.Perm (Fin b)),
          (Nat.card (GroupEpimorphism J (G ⧸ N.val)) : ℝ) := by
      unfold completeQuotientWeight completeQuotientCount
      simp only [Nat.cast_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr (by ext N; simp)
      intro N _
      rfl
    have htotal :
        (∑ N : Ax,∑ J : Subgroup (Equiv.Perm (Fin b)),
          (Nat.card (GroupEpimorphism J (G ⧸ N.val)) : ℝ))≤
        (Nat.card Ax : ℝ)*(BinaryKernelRankTailNumerics.raw 1 536870953 b+
          (subgroupCount b : ℝ)*((2 : ℝ)^(2030 : ℕ)*(2 : ℝ)^(theta*(b : ℝ)))) := by
      calc
        _ ≤ ∑ _N : Ax,(BinaryKernelRankTailNumerics.raw 1 536870953 b+
            (subgroupCount b : ℝ)*((2 : ℝ)^(2030 : ℕ)*(2 : ℝ)^(theta*(b : ℝ)))) :=
          Finset.sum_le_sum (fun N _ => hN N)
        _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_eq_nat_card]
    apply hphysical.trans
    rw [he]
    apply htotal.trans
    calc
      _ ≤ (2 : ℝ)^(1681 : ℕ)*(BinaryKernelRankTailNumerics.raw 1 536870953 b+
          (subgroupCount b : ℝ)*((2 : ℝ)^(2030 : ℕ)*(2 : ℝ)^(theta*(b : ℝ)))) :=
        mul_le_mul_of_nonneg_right hn (by unfold BinaryKernelRankTailNumerics.raw; positivity)
      _ = _ := by
        unfold BinaryKernelRankTailNumerics.raw
        rw [show (3711 : ℕ)=1681+2030 by decide,pow_add]
        ring

/-- All original normal axes have been summed before normalization. -/
def source : PreE7RankTailSourceOrYonedaTopData 24
    (preE7SmallPairNonPairAction 12 (by decide) p) :=
  (data p F ht theta hgap haxisSum).finalSource


end SymmetricSubgroupAsymptotics.TwelvePairOriginalSource
