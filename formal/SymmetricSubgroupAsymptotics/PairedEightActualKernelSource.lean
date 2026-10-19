import SymmetricSubgroupAsymptotics.PairedEightActualKernelQuotientSum
import SymmetricSubgroupAsymptotics.PairedEightActualTopLocator
import SymmetricSubgroupAsymptotics.WidthSixteenBinaryRankTailResidual

/-! Complete width-sixteen sources for physical eight-pair actions.
All original normal axes, top maps and hot fibres are summed internally.
The only classification input is the existing published degree-eight
action catalogue; no 527-action source table is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.PairedEightActualKernelSource
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoPairedEightSharedTops

variable {U : Subgroup (Equiv.Perm (Fin 16))}
    (F : BinaryPairFrame U (Fin 8)) (j : Fin 24)
    (e : F.top.range ≃* (interface j).top)
    (coords : Fin 8 ≃ Fin 8)
    (hact : ∀ (p : F.top.range) (i : Fin 8), coords ((p : Equiv.Perm (Fin 8)) i)=
      (e p : Equiv.Perm (Fin 8)) (coords i))

include hact in
theorem complete_sum_le
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (b : ℕ) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)),completeQuotientWeight (R := U) J) ≤
      (2 : ℝ)^(1216 : ℕ)*(2 : ℝ)^((31/16 : ℝ)*b)*(subgroupCount b : ℝ)+
        BinaryKernelRankTailNumerics.raw ((2 : ℝ)^(576 : ℕ)) 65560 b := by
  let Ax := {N : Subgroup U // N.Normal}
  have hU := PairedEightActualKernelQuotientSum.original_order_le F j e
  have hn : (Nat.card Ax : ℝ) ≤ (2 : ℝ)^(576 : ℕ) := by
    exact_mod_cast normalSubgroup_card_le_two_pow_sq 24 hU
  have hN (N : Ax) :
      (∑ J : Subgroup (Equiv.Perm (Fin b)),(Nat.card (GroupEpimorphism J (U ⧸ N.val)) : ℝ)) ≤
      BinaryKernelRankTailNumerics.raw 1 65560 b+
        (subgroupCount b : ℝ)*((2 : ℝ)^(640 : ℕ)*(2 : ℝ)^((31/16 : ℝ)*b)) := by
    letI := N.property
    exact PairedEightActualKernelQuotientSum.quotient_sum_le F j e coords hact hZmud lit N.val b
  have he :
      (∑ J : Subgroup (Equiv.Perm (Fin b)),completeQuotientWeight (R := U) J)=
      ∑ N : Ax,∑ J : Subgroup (Equiv.Perm (Fin b)),
        (Nat.card (GroupEpimorphism J (U ⧸ N.val)) : ℝ) := by
    unfold completeQuotientWeight completeQuotientCount
    simp only [Nat.cast_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr (by ext N; simp)
    intro N _
    rfl
  rw [he]
  have htotal :
      (∑ N : Ax,∑ J : Subgroup (Equiv.Perm (Fin b)),
        (Nat.card (GroupEpimorphism J (U ⧸ N.val)) : ℝ)) ≤
      (Nat.card Ax : ℝ)*(BinaryKernelRankTailNumerics.raw 1 65560 b+
        (subgroupCount b : ℝ)*((2 : ℝ)^(640 : ℕ)*(2 : ℝ)^((31/16 : ℝ)*b))) := by
    calc
      _ ≤ ∑ _N : Ax,(BinaryKernelRankTailNumerics.raw 1 65560 b+
          (subgroupCount b : ℝ)*((2 : ℝ)^(640 : ℕ)*(2 : ℝ)^((31/16 : ℝ)*b))) :=
        Finset.sum_le_sum (fun N _ => hN N)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_eq_nat_card]
  apply htotal.trans
  calc
    _ ≤ (2 : ℝ)^(576 : ℕ)*(BinaryKernelRankTailNumerics.raw 1 65560 b+
        (subgroupCount b : ℝ)*((2 : ℝ)^(640 : ℕ)*(2 : ℝ)^((31/16 : ℝ)*b))) :=
      mul_le_mul_of_nonneg_right hn (by unfold BinaryKernelRankTailNumerics.raw; positivity)
    _ = _ := by
      unfold BinaryKernelRankTailNumerics.raw
      rw [show (1216 : ℕ)=576+640 by decide,pow_add]
      ring

def sourceData (i : PreE7NonPairActionClass 16)
    (F : BinaryPairFrame (preE7NonPairAction 16 i) (Fin 8)) (j : Fin 24)
    (e : F.top.range ≃* (interface j).top)
    (coords : Fin 8 ≃ Fin 8)
    (hact : ∀ (p : F.top.range) (k : Fin 8), coords ((p : Equiv.Perm (Fin 8)) k)=
      (e p : Equiv.Perm (Fin 8)) (coords k))
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature) :
    WidthSixteenBinaryRankTailResidual.Data 16 i where
  cold := (2 : ℝ)^(1216 : ℕ)
  theta := 31/16
  hot := (2 : ℝ)^(576 : ℕ)
  factorialPower := 65560
  cold_nonneg := by positivity
  hot_nonneg := by positivity
  cold_le := pow_le_pow_right₀ (by norm_num : (1 : ℝ)≤2) (by decide : 1216≤1280)
  width := rfl
  tail_gap := by norm_num [halfDegree,preE7CharacterRho]
  summed := by
    intro b P
    have hphysical :
        (∑ J : Subgroup (Equiv.Perm (Fin b)),fusionCompleteSourceSum (preE7NonPairAction 16 i) P J) ≤
        ∑ J : Subgroup (Equiv.Perm (Fin b)),completeQuotientWeight (R := preE7NonPairAction 16 i) J := by
      apply Finset.sum_le_sum
      intro J _
      unfold fusionCompleteSourceSum completeQuotientWeight completeQuotientCount
      rw [Nat.cast_sum]
      exact Finset.sum_le_sum (fun N _ =>
        fusionSurvivingEpiCount_le_groupEpimorphism_card (preE7NonPairAction 16 i) P N J)
    exact hphysical.trans (complete_sum_le F j e coords hact hZmud lit b)

/-- A uniform source for every original eight-pair representative. -/
def source
    (published : DegreeEightCanonicalCatalogue.PublishedClassification)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (p : PreE7PairActionClass 8) :
    PreE7RankTailSourceOrYonedaTopData 16 (preE7SmallPairNonPairAction 8 (by decide) p) := by
  apply Classical.choice
  obtain ⟨j,e,coords,hact⟩ := PairedEightActualTopLocator.exists_actual_model
    (preE7PairFrame 8 p) published (preE7PairAction_not_isPGroup 8 p)
  exact ⟨(sourceData (preE7SmallPairNonPairAction 8 (by decide) p)
    (preE7PairFrame 8 p) j e coords hact hZmud lit).finalSource⟩

end SymmetricSubgroupAsymptotics.PairedEightActualKernelSource
