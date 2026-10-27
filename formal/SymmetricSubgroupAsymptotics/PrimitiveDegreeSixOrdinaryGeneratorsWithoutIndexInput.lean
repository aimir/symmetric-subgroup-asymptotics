import SymmetricSubgroupAsymptotics.PrimitiveDegreeSixQuotientWithoutIndexInput
import SymmetricSubgroupAsymptotics.CFSGAlternatingGeneration
import SymmetricSubgroupAsymptotics.PrimitiveSocleOneFactorOrdinaryRecurrence
import SymmetricSubgroupAsymptotics.FiniteGroupBinaryOrderGenerators

/-! The actual simple full socle in degree six is A5 or A6 by its
faithful alternating image and proved order. Its actual quotient has
order at most two, so the original group needs at most three generators.
No global simple-index, Tracey or MN premise is supplied. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveDegreeSixOrdinaryGeneratorsWithoutIndexInput
open PrimitiveSocleRawStructure

theorem genRank_le_three {G : Type} [Group G] [Finite G]
    [MulAction G (Fin 6)] [FaithfulSMul G (Fin 6)]
    (D : NonaffineData G (Fin 6)) : MarkedC4.genRank G≤3 := by
  have hk := PrimitiveSocleSevenPointSingleFactorWithoutIndexInput.factorCount_eq_one
    D (by decide) (by decide)
  let S := finiteGroupSocle G
  let eD : S ≃* D.Simple := D.oneFactorEquiv hk
  letI : IsSimpleGroup S := eD.isSimpleGroup
  have hn : ¬IsMulCommutative S := by
    intro hh
    apply D.noncommutative
    apply IsMulCommutative.of_comm
    intro a b
    have he := congrArg eD (hh.is_comm.comm (eD.symm a) (eD.symm b))
    simpa only [map_mul,eD.apply_symm_apply] using he
  letI : Group.IsPerfect S := simple_perfect_of_nonabelian hn
  let j := perfectPermutationToAlternating (MulAction.toPermHom S (Fin 6))
  have hj : Function.Injective j := perfectPermutationToAlternating_injective _
    (show Function.Injective (MulAction.toPermHom S (Fin 6)) from MulAction.toPerm_injective)
  have hSrank : MarkedC4.genRank S≤2 := by
    rcases D.degreeSix_socle_card_without_index with h60 | h360
    · have hH : Nat.card j.range=60 :=
        (Nat.card_congr (MonoidHom.ofInjective hj).toEquiv).symm.trans h60
      let e := (MonoidHom.ofInjective hj).trans
        (PrimitiveDegreeSixRecognition.alternatingSubgroupEquiv j.range hH)
      exact (CoprimeNilpotentProductGenerators.genRank_mulEquiv e).le.trans
        (CFSGAlternatingGeneration.genRank_le_two 5 (by decide))
    · have hH : Nat.card j.range=Nat.card (alternatingGroup (Fin 6)) := by
        rw [PrimitiveDegreeSixRecognition.card_alt_six]
        exact (Nat.card_congr (MonoidHom.ofInjective hj).toEquiv).symm.trans h360
      have htop : j.range=⊤ := j.range.eq_top_of_card_eq hH
      let e : S ≃* alternatingGroup (Fin 6) := (MonoidHom.ofInjective hj).trans
        ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv)
      exact (CoprimeNilpotentProductGenerators.genRank_mulEquiv e).le.trans
        (CFSGAlternatingGeneration.genRank_le_two 6 (by decide))
  have hT : MarkedC4.genRank D.Simple≤2 :=
    (CoprimeNilpotentProductGenerators.genRank_mulEquiv eD).symm.le.trans hSrank
  have hQ : MarkedC4.genRank (G ⧸ finiteGroupSocle G)≤1 :=
    FiniteGroupBinaryOrderGenerators.genRank_le_of_card_le_two_pow _ 1
      (by simpa only [pow_one] using
        PrimitiveDegreeSixOrdinaryWithoutIndexInput.nonaffine_socle_quotient_card_le_two D)
  have hr := PrimitiveSocleOneFactorOrdinaryRecurrence.genRank_le_simple_add_actual_quotient D hk
  omega

end SymmetricSubgroupAsymptotics.PrimitiveDegreeSixOrdinaryGeneratorsWithoutIndexInput
