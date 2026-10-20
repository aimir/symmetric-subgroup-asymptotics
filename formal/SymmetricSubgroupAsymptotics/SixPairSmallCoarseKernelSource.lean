import SymmetricSubgroupAsymptotics.SixPairSmallCoarseKernelQuotientSum
import SymmetricSubgroupAsymptotics.BinaryKernelRankTailResidual
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairGeneralSourceAssembly

/-! Complete representative-facing width-twelve source when the actual
three-pair coarse kernel has order at most four. Every original normal
axis is summed internally; C4 and nonsplit extensions are retained. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.SixPairSmallCoarseKernelSource
open Non2UnipotentPrefixFiniteMenu

variable (p : PreE7PairActionClass 6)
  [MulAction.IsPretransitive (preE7PairAction 6 p) (Fin 12)]
  (F : BinaryPairFrame (preE7PairAction 6 p) (Fin 6))
  (E : ProductBlockFrame F.top.range (Fin 3) (ZMod 2))
  (hcard : Nat.card (SixPairNestedTopFrames.nestedFrame F E).top.ker≤4)
  (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)

def data : BinaryKernelRankTailResidual.Data 12 (preE7SixPairNonPairAction p) where
  cold := (2 : ℝ)^(89 : ℕ)
  theta := 43/30
  hot := (2 : ℝ)^(25 : ℕ)
  factorialPower := 11
  cold_nonneg := by positivity
  hot_nonneg := by positivity
  cold_le := pow_le_pow_right₀ (by norm_num : (1 : ℝ)≤2) (by decide : 89≤512)
  width := Or.inl rfl
  tail_gap := by norm_num [halfDegree,preE7CharacterRho]
  summed := by
    intro b P
    let G := preE7PairAction 6 p
    let Ax := {N : Subgroup G // N.Normal}
    have hU : Nat.card G≤2^5 :=
      SixPairSmallCoarseKernelQuotientSum.original_order_le_five F E hcard
    have hn : (Nat.card Ax : ℝ)≤(2 : ℝ)^(25 : ℕ) := by
      exact_mod_cast normalSubgroup_card_le_two_pow_sq 5 hU
    have hN (N : Ax) :
        (∑ J : Subgroup (Equiv.Perm (Fin b)),(Nat.card (GroupEpimorphism J (G ⧸ N.val)) : ℝ))≤
        BinaryKernelRankTailNumerics.raw 1 11 b+
          (subgroupCount b : ℝ)*((2 : ℝ)^(64 : ℕ)*(2 : ℝ)^((43/30 : ℝ)*(b : ℝ))) :=
      SixPairSmallCoarseKernelQuotientSum.quotient_sum_le F E hcard hZmud lit N.val b
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
        (Nat.card Ax : ℝ)*(BinaryKernelRankTailNumerics.raw 1 11 b+
          (subgroupCount b : ℝ)*((2 : ℝ)^(64 : ℕ)*(2 : ℝ)^((43/30 : ℝ)*(b : ℝ)))) := by
      calc
        _ ≤ ∑ _N : Ax,(BinaryKernelRankTailNumerics.raw 1 11 b+
            (subgroupCount b : ℝ)*((2 : ℝ)^(64 : ℕ)*(2 : ℝ)^((43/30 : ℝ)*(b : ℝ)))) :=
          Finset.sum_le_sum (fun N _ => hN N)
        _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_eq_nat_card]
    apply hphysical.trans
    rw [he]
    apply htotal.trans
    calc
      _ ≤ (2 : ℝ)^(25 : ℕ)*(BinaryKernelRankTailNumerics.raw 1 11 b+
          (subgroupCount b : ℝ)*((2 : ℝ)^(64 : ℕ)*(2 : ℝ)^((43/30 : ℝ)*(b : ℝ)))) :=
        mul_le_mul_of_nonneg_right hn (by unfold BinaryKernelRankTailNumerics.raw; positivity)
      _ = _ := by unfold BinaryKernelRankTailNumerics.raw; ring

/-- Actual all-original-axis source from an actual small coarse kernel. -/
def source : PreE7RankTailSourceOrYonedaTopData 12 (preE7SixPairNonPairAction p) :=
  (data p F E hcard hZmud lit).finalSource

end SymmetricSubgroupAsymptotics.SixPairSmallCoarseKernelSource
