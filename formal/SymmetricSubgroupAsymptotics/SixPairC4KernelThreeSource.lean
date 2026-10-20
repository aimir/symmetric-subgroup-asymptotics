import SymmetricSubgroupAsymptotics.SixPairC4KernelThreeQuotientSum
import SymmetricSubgroupAsymptotics.MixedKernelRankTailResidual
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairGeneralSourceAssembly

/-! Complete representative-facing width-twelve source when the actual
three-pair coarse kernel embeds in C4³. Every original normal axis is
summed internally; the kernel is not required to be elementary or split. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.SixPairC4KernelThreeSource
open Non2UnipotentPrefixFiniteMenu

variable (p : PreE7PairActionClass 6)
  [MulAction.IsPretransitive (preE7PairAction 6 p) (Fin 12)]
  (F : BinaryPairFrame (preE7PairAction 6 p) (Fin 6))
  (E : ProductBlockFrame F.top.range (Fin 3) (ZMod 2))
  (j : (SixPairNestedTopFrames.nestedFrame F E).top.ker →* (Fin 3 → C4CoordinateHomCount.C4))
  (hj : Function.Injective j)
  (hKP : KovacsPraegerAbelianizationBound)

def data : MixedKernelRankTailResidual.Data 12 (preE7SixPairNonPairAction p) where
  cold := (2 : ℝ)^(161 : ℕ)
  theta := 43/30
  hotBinary := 0
  factorialPowerBinary := 0
  hotC4 := (2 : ℝ)^(81 : ℕ)
  factorialPowerC4 := 15
  cold_nonneg := by positivity
  hotBinary_nonneg := le_rfl
  hotC4_nonneg := by positivity
  cold_le := pow_le_pow_right₀ (by norm_num : (1 : ℝ)≤2) (by decide : 161≤512)
  width := Or.inl rfl
  tail_gap := by norm_num [halfDegree,preE7CharacterRho]
  summed := by
    intro b P
    let G := preE7PairAction 6 p
    let Ax := {N : Subgroup G // N.Normal}
    have hU : Nat.card G≤2^9 :=
      SixPairC4KernelThreeQuotientSum.original_order_le_nine F E j hj
    have hn : (Nat.card Ax : ℝ)≤(2 : ℝ)^(81 : ℕ) := by
      exact_mod_cast normalSubgroup_card_le_two_pow_sq 9 hU
    have hN (N : Ax) :
        (∑ J : Subgroup (Equiv.Perm (Fin b)),(Nat.card (GroupEpimorphism J (G ⧸ N.val)) : ℝ))≤
        MarkedC4KernelRankTailNumerics.raw 1 15 b+
          (subgroupCount b : ℝ)*((2 : ℝ)^(80 : ℕ)*(2 : ℝ)^((43/30 : ℝ)*(b : ℝ))) :=
      SixPairC4KernelThreeQuotientSum.quotient_sum_le F E j hj hKP N.val b
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
        (Nat.card Ax : ℝ)*(MarkedC4KernelRankTailNumerics.raw 1 15 b+
          (subgroupCount b : ℝ)*((2 : ℝ)^(80 : ℕ)*(2 : ℝ)^((43/30 : ℝ)*(b : ℝ)))) := by
      calc
        _ ≤ ∑ _N : Ax,(MarkedC4KernelRankTailNumerics.raw 1 15 b+
            (subgroupCount b : ℝ)*((2 : ℝ)^(80 : ℕ)*(2 : ℝ)^((43/30 : ℝ)*(b : ℝ)))) :=
          Finset.sum_le_sum (fun N _ => hN N)
        _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_eq_nat_card]
    apply hphysical.trans
    rw [he]
    apply htotal.trans
    calc
      _ ≤ (2 : ℝ)^(81 : ℕ)*(MarkedC4KernelRankTailNumerics.raw 1 15 b+
          (subgroupCount b : ℝ)*((2 : ℝ)^(80 : ℕ)*(2 : ℝ)^((43/30 : ℝ)*(b : ℝ)))) :=
        mul_le_mul_of_nonneg_right hn (by
          have hm : 0 ≤ markedC4Moment b (MarkedC4KernelRankTailNumerics.tilt b) := by
            unfold markedC4Moment
            exact Finset.sum_nonneg (fun _ _ => by positivity)
          unfold MarkedC4KernelRankTailNumerics.raw
          positivity)
      _ = _ := by
        unfold BinaryKernelRankTailNumerics.raw MarkedC4KernelRankTailNumerics.raw
        ring

/-- Actual all-original-axis source from actual C4³ kernel coordinates. -/
def source (hM4 : GlobalMarkedC4MomentBound) :
    PreE7RankTailSourceOrYonedaTopData 12 (preE7SixPairNonPairAction p) :=
  (data p F E j hj hKP).finalSource hM4

end SymmetricSubgroupAsymptotics.SixPairC4KernelThreeSource
