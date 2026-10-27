import SymmetricSubgroupAsymptotics.SevenPointTransitiveSimpleOrderDichotomy
import SymmetricSubgroupAsymptotics.PrimitiveSocleSevenPointSingleFactorWithoutIndexInput
import SymmetricSubgroupAsymptotics.OneFactorSocleEightCosetOrdinaryGenerators
import SymmetricSubgroupAsymptotics.NaturalDegreeFiveSocleOrdinaryGenerators

/-! Original nonaffine seven-point groups have ordinary rank at most3.
Socle168 uses the ORIGINAL ambient normalizer coset action of degree8,
including any outer extension; socle2520 gives actual A7≤imageG≤S7.
The original group is never silently assumed simple or even. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveDegreeSevenOrdinaryGeneratorsWithoutIndexInput
open PrimitiveSocleRawStructure
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

theorem genRank_le_three (hCFSG : CFSG.CFSGClassification)
    {G : Type} [Group G] [Finite G] [MulAction G (Fin 7)]
    [FaithfulSMul G (Fin 7)] (D : NonaffineData G (Fin 7)) :
    MarkedC4.genRank G≤3 := by
  have hk := PrimitiveSocleSevenPointSingleFactorWithoutIndexInput.factorCount_eq_one
    D (by decide) (by decide)
  let S := finiteGroupSocle G
  let eS := D.oneFactorEquiv hk
  letI : IsSimpleGroup S := eS.isSimpleGroup
  letI : MulAction.IsPretransitive S (Fin 7) := D.socle_transitive
  have hnS : ¬IsMulCommutative S := by
    intro hh
    apply D.noncommutative
    apply IsMulCommutative.of_comm
    intro a b
    have he := congrArg eS (hh.is_comm.comm (eS.symm a) (eS.symm b))
    simpa only [map_mul,eS.apply_symm_apply] using he
  rcases SevenPointTransitiveSimpleOrderDichotomy.card_eq_168_or_2520 hCFSG hnS with h168 | h2520
  · let P : Sylow 7 S := Classical.choice inferInstance
    have hP : Nat.card P=7 := by rw [P.card_eq_multiplicity,h168]; decide +kernel
    let NS := Subgroup.normalizer (P : Set S)
    have hNS : Nat.card NS=21 :=
      SevenPointSimpleSylowNormalizerExact.normalizer_card_eq_twentyOne hnS P hP
    have hidx : NS.index=8 := by
      have hh := NS.card_mul_index
      rw [hNS,h168] at hh
      omega
    let N := Subgroup.normalizer ((P.map S.subtype : Subgroup G) : Set G)
    have hN8 : N.index=8 :=
      (NormalSubgroupSylowNormalizerIndex.index_eq S P).trans hidx
    exact OneFactorSocleEightCosetOrdinaryGenerators.genRank_le_three D hk N hN8
      (Sylow.normalizer_sup_eq_top P)
  · letI : Group.IsPerfect S := simple_perfect_of_nonabelian hnS
    let rho := MulAction.toPermHom G (Fin 7)
    have hrho : Function.Injective rho := MulAction.toPerm_injective
    let j := perfectPermutationToAlternating (MulAction.toPermHom S (Fin 7))
    have hj : Function.Injective j := perfectPermutationToAlternating_injective _
      (show Function.Injective (MulAction.toPermHom S (Fin 7)) from MulAction.toPerm_injective)
    have hcard : Nat.card j.range=Nat.card (alternatingGroup (Fin 7)) := by
      have he : Nat.card (alternatingGroup (Fin 7))=2520 := by
        rw [nat_card_alternatingGroup,Nat.card_fin]; decide
      exact (Nat.card_congr (MonoidHom.ofInjective hj).toEquiv).symm.trans (h2520.trans he.symm)
    have htop : j.range=⊤ := j.range.eq_top_of_card_eq hcard
    have hA : alternatingGroup (Fin 7)≤rho.range := by
      intro a ha
      have hjmem : (⟨a,ha⟩ : alternatingGroup (Fin 7)) ∈ j.range := by rw [htop]; trivial
      obtain ⟨s,hs⟩ := hjmem
      refine ⟨s.val,?_⟩
      exact congrArg Subtype.val hs
    letI : IsSimpleGroup (alternatingGroup (Fin 7)) :=
      alternatingGroup.isSimpleGroup (by simp only [Nat.card_fin]; decide)
    have hR : MarkedC4.genRank rho.range≤2 := by
      rcases indexTwo_maximal (alternatingGroup (Fin 7)) alternatingGroup.index_eq_two rho.range hA with hAlt | hAll
      · rw [hAlt]
        exact CFSGAlternatingGeneration.genRank_le_two 7 (by decide)
      · let e : rho.range ≃* Equiv.Perm (Fin 7) :=
          (MulEquiv.subgroupCongr hAll).trans Subgroup.topEquiv
        exact (CoprimeNilpotentProductGenerators.genRank_mulEquiv e).le.trans
          (NaturalDegreeFiveSocleOrdinaryGenerators.symmetric_genRank_le_two 7 (by decide))
    exact ((CoprimeNilpotentProductGenerators.genRank_mulEquiv (MonoidHom.ofInjective hrho)).le.trans hR).trans (by decide)

end SymmetricSubgroupAsymptotics.PrimitiveDegreeSevenOrdinaryGeneratorsWithoutIndexInput
