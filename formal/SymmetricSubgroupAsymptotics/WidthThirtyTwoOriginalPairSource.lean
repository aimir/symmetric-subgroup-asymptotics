import SymmetricSubgroupAsymptotics.WidthThirtyTwoActualKernelQuotientSum
import SymmetricSubgroupAsymptotics.WidthThirtyTwoBinaryRankTailResidual
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairGeneralSourceAssembly

/-! Complete original-axis aggregation at width32. The geometric
constructors below consume proved bounds on the actual top and its natural
module; no finite catalogue completeness or source bound is a literature
assumption. The split constructor charges binary targets separately. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.WidthThirtyTwoOriginalPairSource
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

variable (p : PreE7PairActionClass 16)
  (F : BinaryPairFrame (preE7PairAction 16 p) (Fin 16))
  (ht : Nat.card F.top.range≤2^32) (theta : ℝ)
  (hgap : theta≤(halfDegree 32 : ℝ)/4-preE7CharacterRho*32/4)
  (haxisSum : ∀ (N : Subgroup (preE7PairAction 16 p)) [N.Normal] (b : ℕ),
    (∑ J : Subgroup (Equiv.Perm (Fin b)),
      (Nat.card (GroupEpimorphism J (preE7PairAction 16 p ⧸ N)) : ℝ)) ≤
      BinaryKernelRankTailNumerics.raw 1 4294967344 b+
        (subgroupCount b : ℝ)*((2 : ℝ)^(2560 : ℕ)*(2 : ℝ)^(theta*b)))

def data : WidthThirtyTwoBinaryRankTailResidual.Data 32 (preE7SmallPairNonPairAction 16 (by decide) p) where
  cold := (2 : ℝ)^(4864 : ℕ)
  theta := theta
  hot := (2 : ℝ)^(2304 : ℕ)
  factorialPower := 4294967344
  cold_nonneg := by positivity
  hot_nonneg := by positivity
  cold_le := pow_le_pow_right₀ (by norm_num : (1 : ℝ)≤2) (by decide : 4864≤5000)
  width := rfl
  tail_gap := hgap
  summed := by
    intro b P
    let G := preE7PairAction 16 p
    let Ax := {N : Subgroup G // N.Normal}
    have hU : Nat.card G≤2^48 :=
      WidthThirtyTwoActualKernelQuotientSum.original_order_le F ht
    have hn : (Nat.card Ax : ℝ)≤(2 : ℝ)^(2304 : ℕ) := by
      exact_mod_cast normalSubgroup_card_le_two_pow_sq 48 hU
    have hN (N : Ax) :
        (∑ J : Subgroup (Equiv.Perm (Fin b)),(Nat.card (GroupEpimorphism J (G ⧸ N.val)) : ℝ))≤
        BinaryKernelRankTailNumerics.raw 1 4294967344 b+
          (subgroupCount b : ℝ)*((2 : ℝ)^(2560 : ℕ)*(2 : ℝ)^(theta*(b : ℝ))) :=
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
        (Nat.card Ax : ℝ)*(BinaryKernelRankTailNumerics.raw 1 4294967344 b+
          (subgroupCount b : ℝ)*((2 : ℝ)^(2560 : ℕ)*(2 : ℝ)^(theta*(b : ℝ)))) := by
      calc
        _ ≤ ∑ _N : Ax,(BinaryKernelRankTailNumerics.raw 1 4294967344 b+
            (subgroupCount b : ℝ)*((2 : ℝ)^(2560 : ℕ)*(2 : ℝ)^(theta*(b : ℝ)))) :=
          Finset.sum_le_sum (fun N _ => hN N)
        _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_eq_nat_card]
    apply hphysical.trans
    rw [he]
    apply htotal.trans
    calc
      _ ≤ (2 : ℝ)^(2304 : ℕ)*(BinaryKernelRankTailNumerics.raw 1 4294967344 b+
          (subgroupCount b : ℝ)*((2 : ℝ)^(2560 : ℕ)*(2 : ℝ)^(theta*(b : ℝ)))) :=
        mul_le_mul_of_nonneg_right hn (by unfold BinaryKernelRankTailNumerics.raw; positivity)
      _ = _ := by
        unfold BinaryKernelRankTailNumerics.raw
        rw [show (4864 : ℕ)=2304+2560 by decide,pow_add]
        ring

/-- All original normal axes have been summed before normalization. -/
def source : PreE7RankTailSourceOrYonedaTopData 32
    (preE7SmallPairNonPairAction 16 (by decide) p) :=
  (data p F ht theta hgap haxisSum).finalSource

/-- A geometric all-quotient socle theorem and the actual natural-module
bound construct the complete source, with no epimorphism estimate as input. -/
def of_uniform_socle {k H : ℕ}
    (hu : UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) F.top.range (Fin 16)) H)
    (hsocle : ∀ (M : Subgroup F.top.range) [M.Normal],
      SocleNormalGeneratorBound (F.top.range ⧸ M) k)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (hslope : (k : ℝ)*(Real.logb 2 5/3)+(51/200 : ℝ)*H≤theta) :
    PreE7RankTailSourceOrYonedaTopData 32
      (preE7SmallPairNonPairAction 16 (by decide) p) :=
  source p F ht theta hgap (fun N _ b =>
    WidthThirtyTwoActualKernelQuotientSum.quotient_sum_le F ht hu hsocle
      hZmud lit theta hslope N b)

/-- The nonbinary residual top uses its socle theorem; binary original
targets retain the separately proved order bound. -/
def of_split_socle {k H : ℕ}
    (hu : UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) F.top.range (Fin 16)) H)
    (hsocle : ∀ (M : Subgroup F.top.range) [M.Normal],
      ¬IsPGroup 2 (F.top.range ⧸ M) → SocleNormalGeneratorBound (F.top.range ⧸ M) k)
    (hbinary : ∀ (N : Subgroup (preE7PairAction 16 p)) [N.Normal],
      IsPGroup 2 (preE7PairAction 16 p ⧸ N) → Nat.card (preE7PairAction 16 p ⧸ N)≤2^15)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (hslope : (k : ℝ)*(Real.logb 2 5/3)+(51/200 : ℝ)*H≤theta)
    (hbinarySlope : (15 : ℝ)*(51/200)≤theta) :
    PreE7RankTailSourceOrYonedaTopData 32
      (preE7SmallPairNonPairAction 16 (by decide) p) :=
  source p F ht theta hgap (fun N _ b =>
    WidthThirtyTwoActualKernelQuotientSum.quotient_sum_le_of_split F ht hu hsocle
      hbinary hZmud lit theta hslope hbinarySlope N b)

end SymmetricSubgroupAsymptotics.WidthThirtyTwoOriginalPairSource
