import SymmetricSubgroupAsymptotics.BoundedSharpJankoTwoHeisenbergSingerCompleteCFSG
import SymmetricSubgroupAsymptotics.ExtendedCatalogueSmallDegreeModels
import SymmetricSubgroupAsymptotics.ExtendedCatalogueOddOrderSolvability
import SymmetricSubgroupAsymptotics.TraceyPublished2018PermutationBundle

/-! Internal bounded-sharp assembly for the actual extended classification target.
The proof reuses the literal original action, residual structures, failed-half
witnesses, all tag guards, and checked finite prime certificates. Only the
classification funnels and the odd-order backend change. The raw Y443 branch
is excluded by degree before entering any old-model residual. This module does
not construct Classification or add it as a public T1 assumption. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.SevenPointTransitiveSimpleOrderDichotomy
open _root_.SymmetricSubgroupAsymptotics.SevenPointTransitiveSimpleOrderDichotomy
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
private theorem divisor_receipt : ∀ k : Fin 121, k.val ∣ 120 → k.val % 7=1 →
    k.val=1 ∨ k.val=8 ∨ k.val=15 ∨ k.val=120 := by decide +kernel

theorem card_eq_168_or_2520 (hclass : CFSGCatalogueWithAxiomMonster.Classification)
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    [MulAction G (Fin 7)] [FaithfulSMul G (Fin 7)]
    [MulAction.IsPretransitive G (Fin 7)] (hn : ¬IsMulCommutative G) :
    Nat.card G=168 ∨ Nat.card G=2520 := by
  letI : Group.IsPerfect G := simple_perfect_of_nonabelian hn
  let j := perfectPermutationToAlternating (MulAction.toPermHom G (Fin 7))
  have hj : Function.Injective j := perfectPermutationToAlternating_injective _
    (show Function.Injective (MulAction.toPermHom G (Fin 7)) from MulAction.toPerm_injective)
  have hd : Nat.card G ∣ 2520 := by
    have hh := Subgroup.card_dvd_of_injective j hj
    simpa only [nat_card_alternatingGroup,Nat.card_fin] using hh
  have hseven : 7 ∣ Nat.card G := by
    have hi : Nat.card (Fin 7) ∣ Nat.card G := by
      rw [←MulAction.index_stabilizer_of_transitive G (0 : Fin 7)]
      exact Subgroup.index_dvd_card _
    simpa only [Nat.card_fin] using hi
  have hval : (Nat.card G).factorization 7=1 := by
    have hhi := (Nat.factorization_le_iff_dvd Nat.card_pos.ne' (by decide : 2520 ≠ 0)).mpr hd 7
    have hlo := (Nat.Prime.dvd_iff_one_le_factorization (by decide : Nat.Prime 7) Nat.card_pos.ne').mp hseven
    have he : (2520 : ℕ).factorization 7=1 := by decide +kernel
    rw [he] at hhi
    omega
  let P : Sylow 7 G := Classical.choice inferInstance
  have hP : Nat.card P=7 := by rw [P.card_eq_multiplicity,hval,pow_one]
  have hN := SevenPointSimpleSylowNormalizerExact.normalizer_card_eq_twentyOne hn P hP
  have hm : 21*Nat.card (Sylow 7 G)=Nat.card G := by
    have hh := (Subgroup.normalizer (P : Set G)).card_mul_index
    rw [←P.card_eq_index_normalizer,hN] at hh
    exact hh
  have hdiv : Nat.card (Sylow 7 G) ∣ 120 := by
    apply (Nat.mul_dvd_mul_iff_left (by decide : 0 < 21)).mp
    simpa only [hm,show 21*120=2520 by decide] using hd
  have hmod : Nat.card (Sylow 7 G)%7=1 := by
    have hh := card_sylow_modEq_one 7 G
    change Nat.card (Sylow 7 G)%7=1%7 at hh
    simpa only [show 1%7=1 by decide] using hh
  have hle := Nat.le_of_dvd (by decide : 0 < 120) hdiv
  have hge := SimplePrimeSylowSuccessorIndexSquare.sylow_count_ge_prime_succ hn P hP
  rcases divisor_receipt ⟨Nat.card (Sylow 7 G),by omega⟩ hdiv hmod with h1 | h8 | h15 | h120
  · change Nat.card (Sylow 7 G) = 1 at h1
    omega
  · change Nat.card (Sylow 7 G) = 8 at h8
    exact Or.inl (by rw [←hm,h8])
  · change Nat.card (Sylow 7 G) = 15 at h15
    have ho : Nat.card G=315 := by rw [←hm,h15]
    letI : IsSolvable G := ExtendedCatalogueOddOrderSolvability.odd_order_solvable hclass G
      (by rw [ho]; decide)
    exact (hn (isMulCommutative_iff.mpr (IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance))).elim
  · change Nat.card (Sylow 7 G) = 120 at h120
    exact Or.inr (by rw [←hm,h120])
end SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.SevenPointTransitiveSimpleOrderDichotomy

namespace SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.PrimitiveDegreeSevenOrdinaryGeneratorsWithoutIndexInput
open _root_.SymmetricSubgroupAsymptotics.PrimitiveDegreeSevenOrdinaryGeneratorsWithoutIndexInput
open PrimitiveSocleRawStructure
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

theorem genRank_le_three (hclass : CFSGCatalogueWithAxiomMonster.Classification)
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
  rcases _root_.SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.SevenPointTransitiveSimpleOrderDichotomy.card_eq_168_or_2520 hclass hnS with h168 | h2520
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
          (_root_.SymmetricSubgroupAsymptotics.NaturalDegreeFiveSocleOrdinaryGenerators.symmetric_genRank_le_two 7 (by decide))
    exact ((CoprimeNilpotentProductGenerators.genRank_mulEquiv (MonoidHom.ofInjective hrho)).le.trans hR).trans (by decide)
end SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.PrimitiveDegreeSevenOrdinaryGeneratorsWithoutIndexInput

namespace SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.EightPointHalfDegreeCompleteCFSG
open _root_.SymmetricSubgroupAsymptotics.EightPointHalfDegreeCompleteCFSG
open _root_.SymmetricSubgroupAsymptotics.EightPointHalfDegreeFiniteModelReduction

theorem no_primitive_sporadic_counterexample_eight (hclass : CFSGCatalogueWithAxiomMonster.Classification) :
    ¬Nonempty (PrimitiveSporadicCounterexample 8) := by
  rintro ⟨w⟩
  have hd := EightPointMinimalFailureDegreeSixOrSeven.degree_eq_six_or_seven w
  rcases w with ⟨d,hlo,hhi,J,ht,hp,hbad,hmin,D,s,e⟩
  change d=6 ∨ d=7 at hd
  rcases hd with h6 | h7
  · subst d
    have hr := PrimitiveDegreeSixOrdinaryGeneratorsWithoutIndexInput.genRank_le_three D
    omega
  · subst d
    have hr := _root_.SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.PrimitiveDegreeSevenOrdinaryGeneratorsWithoutIndexInput.genRank_le_three hclass D
    omega

theorem no_cumulative_global_counterexample_eight (hclass : CFSGCatalogueWithAxiomMonster.Classification) :
    ¬Nonempty (_root_.SymmetricSubgroupAsymptotics.OriginalAffineBoundedSharpCoTwoTopRefinement.CumulativeGlobalCounterexample 8) := by
  rintro ⟨w⟩
  exact no_primitive_sporadic_counterexample_eight hclass ⟨w.val⟩
end SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.EightPointHalfDegreeCompleteCFSG

namespace SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.NaturalDegreeFiveSocleOrdinaryGenerators
open _root_.SymmetricSubgroupAsymptotics.NaturalDegreeFiveSocleOrdinaryGenerators
open PrimitiveSocleRawStructure PrimitiveSocleLargeOneFactorOrdinaryCFSGReduction
open TraceySharpHalfDegreeNumerics

variable (J : Subgroup (Equiv.Perm (Fin 5))) (D : NonaffineData J (Fin 5))

theorem genRank_le_sharpFloor_or_actual_remaining_model (hclass : CFSGCatalogueWithAxiomMonster.Classification) :
    MarkedC4.genRank J ≤ sharpFloor 5 ∨
      ∃ j : CFSG.Index, RemainingModel j ∧ Nonempty (D.Simple ≃* j.Model) := by
  rcases ExtendedCatalogueSmallDegreeModels.factor_packet_or_actual_remaining_of_degree_below_twentySeven D hclass (by simp only [Nat.card_fin]; decide) with hp | hm
  · obtain ⟨ell,hell⟩ := exists_leastProperIndex D.Simple
    exact Or.inl ((genRank_le_two_of_actual_index_square J D ell hell (hp ell hell).1).trans
      two_le_sharpFloor_five)
  · exact Or.inr hm
end SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.NaturalDegreeFiveSocleOrdinaryGenerators

namespace SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.PrimitiveBoundedSharpElevenToTwentyOneCFSGReduction
open _root_.SymmetricSubgroupAsymptotics.PrimitiveBoundedSharpElevenToTwentyOneCFSGReduction
open PrimitiveSocleRawStructure TraceySharpHalfDegreeNumerics
open PrimitiveSocleLargeOneFactorOrdinaryCFSGReduction
open OriginalNonaffinePairFamiliesBlockOrdinaryStep (PairFamily)

private theorem prime_of_prime_power_band (p d n : ℕ) (hp : p.Prime)
    (heq : n = p^d) (hlo : 11 ≤ n) (hhi : n ≤ 21) (h16 : n ≠ 16) : n.Prime := by
  have hdpos : 1 ≤ d := by
    by_contra hh
    have hd0 : d = 0 := by omega
    rw [hd0,pow_zero] at heq
    omega
  by_cases hd1 : d = 1
  · simpa only [heq,hd1,pow_one] using hp
  have hd2 : 2 ≤ d := by omega
  have hp5 : p < 5 := by
    by_contra hh
    have hpow : 25 ≤ p^d := (Nat.pow_le_pow_left (show 5 ≤ p by omega) 2).trans
      (Nat.pow_le_pow_right hp.pos hd2)
    rw [← heq] at hpow
    omega
  have hcases : p = 2 ∨ p = 3 := by
    have hp2 := hp.two_le
    have hp4 : p ≠ 4 := by
      intro he
      have hh := hp
      rw [he] at hh
      norm_num at hh
    omega
  rcases hcases with rfl | rfl
  · have hdle : d ≤ 4 := by
      by_contra hh
      have hpow : 32 ≤ 2^d := Nat.pow_le_pow_right (by decide : 0 < 2) (show 5 ≤ d by omega)
      rw [← heq] at hpow
      omega
    have hdge : 4 ≤ d := by
      by_contra hh
      have hpow : 2^d ≤ 8 := Nat.pow_le_pow_right (by decide : 0 < 2) (show d ≤ 3 by omega)
      rw [← heq] at hpow
      omega
    have hd : d = 4 := by omega
    exact (h16 (by simpa only [hd] using heq)).elim
  · have hdle : d ≤ 2 := by
      by_contra hh
      have hpow : 27 ≤ 3^d := Nat.pow_le_pow_right (by decide : 0 < 3) (show 3 ≤ d by omega)
      rw [← heq] at hpow
      omega
    have hd : d = 2 := by omega
    rw [hd] at heq
    norm_num at heq
    omega

section Nonaffine
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X)

end Nonaffine

theorem genRank_le_sharpFloor_or_actual_residual
    (hclass : CFSGCatalogueWithAxiomMonster.Classification) (n : ℕ) (hlo : 11 ≤ n) (hhi : n ≤ 21)
    (J : Subgroup (Equiv.Perm (Fin n))) (hprimitive : MulAction.IsPreprimitive J (Fin n)) :
    MarkedC4.genRank J ≤ sharpFloor n ∨
      (n = 16 ∧ Nonempty (PrimitiveAffineProfile J (Fin n))) ∨
      ∃ D : NonaffineData J (Fin n), ∃ j : CFSG.Index,
        RemainingModel j ∧ Nonempty (D.Simple ≃* j.Model) := by
  letI : Nontrivial (Fin n) := Finite.one_lt_card_iff_nontrivial.mp
    (by simpa only [Nat.card_fin] using (show 1 < n by omega))
  letI : MulAction.IsPreprimitive J (Fin n) := hprimitive
  obtain ⟨P⟩ := publishedONanScottStructure J (Fin n)
  cases P with
  | inr P =>
      by_cases h16 : n = 16
      · exact Or.inr (Or.inl ⟨h16,⟨P⟩⟩)
      obtain ⟨d,hd⟩ := P.degree_eq_prime_power (⟨0,by omega⟩ : Fin n)
      have hp := prime_of_prime_power_band P.p d n P.p_prime hd hlo hhi h16
      have hg := PrimitiveAffinePrimeOrdinaryGenerators.genRank_le_two P hprimitive hp
      exact Or.inl (hg.trans ((by decide : 2 ≤ 5).trans (five_le_sharpFloor_of_band n hlo hhi)))
  | inl D =>
      rcases ExtendedCatalogueSmallDegreeModels.pair_family_or_actual_remaining_of_degree_below_twenty_four
        D hclass (by simpa only [Nat.card_fin] using (show n < 24 by omega)) with ⟨j,hj,⟨e⟩⟩ | hm
      · have hlow : 11 ≤ Nat.card (Fin n) := by simpa only [Nat.card_fin] using hlo
        have hhigh : Nat.card (Fin n) ≤ 21 := by simpa only [Nat.card_fin] using hhi
        have hg := genRank_le_sharpFloor_of_pair_family D j hj e hlow hhigh
        exact Or.inl (by simpa only [Nat.card_fin] using hg)
      · obtain ⟨j,hj,e⟩ := hm
        exact Or.inr (Or.inr ⟨D,j,hj,e⟩)
end SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.PrimitiveBoundedSharpElevenToTwentyOneCFSGReduction

namespace SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.PrimitiveSocleSixToTenSharpCFSGReduction
open _root_.SymmetricSubgroupAsymptotics.PrimitiveSocleSixToTenSharpCFSGReduction
open PrimitiveSocleRawStructure TraceySharpHalfDegreeNumerics
open PrimitiveSocleLargeOneFactorOrdinaryCFSGReduction
open OriginalNonaffinePairFamiliesBlockOrdinaryStep (PairFamily)


variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] (D : NonaffineData G X)

theorem genRank_le_sharpFloor_or_actual_remaining_model (hclass : CFSGCatalogueWithAxiomMonster.Classification)
    (hlo : 6 ≤ Nat.card X) (hhi : Nat.card X ≤ 10) :
    MarkedC4.genRank G ≤ sharpFloor (Nat.card X) ∨
      ∃ j : CFSG.Index, RemainingModel j ∧ Nonempty (D.Simple ≃* j.Model) := by
  rcases ExtendedCatalogueSmallDegreeModels.pair_family_or_actual_remaining_of_degree_below_twenty_four
    D hclass (by omega) with ⟨j,hj,⟨e⟩⟩ | hm
  · exact Or.inl ((genRank_le_small_of_pair_family D j hj e hlo hhi).trans
      (smallRank_le_sharpFloor (Nat.card X) hlo hhi))
  · exact Or.inr hm
end SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.PrimitiveSocleSixToTenSharpCFSGReduction

namespace SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.PrimitiveBoundedSharpCFSGReduction
open _root_.SymmetricSubgroupAsymptotics.PrimitiveBoundedSharpCFSGReduction
open PrimitiveSocleRawStructure TraceySharpHalfDegreeNumerics
open PrimitiveSocleLargeOneFactorOrdinaryCFSGReduction

private theorem two_le_sharpFloor_of_band (n : ℕ) (hlo : 4 ≤ n) (hhi : n ≤ 21) :
    2 ≤ sharpFloor n := by
  by_cases h4 : n = 4
  · subst n
    exact two_le_sharpFloor_four
  by_cases h5 : n = 5
  · subst n
    exact _root_.SymmetricSubgroupAsymptotics.NaturalDegreeFiveSocleOrdinaryGenerators.two_le_sharpFloor_five
  by_cases hsmall : n ≤ 10
  · have hh := _root_.SymmetricSubgroupAsymptotics.PrimitiveSocleSixToTenSharpCFSGReduction.smallRank_le_sharpFloor
      n (by omega) hsmall
    have htwo : 2 ≤ if n ≤ 7 then 3 else 4 := by split_ifs <;> decide
    exact htwo.trans hh
  · exact (by decide : 2 ≤ 5).trans
      (_root_.SymmetricSubgroupAsymptotics.PrimitiveBoundedSharpElevenToTwentyOneCFSGReduction.five_le_sharpFloor_of_band
        n (by omega) hhi)

theorem genRank_le_sharpFloor_or_actual_residual
    (hclass : CFSGCatalogueWithAxiomMonster.Classification) (n : ℕ) (hlo : 4 ≤ n) (hhi : n ≤ 21)
    (J : Subgroup (Equiv.Perm (Fin n))) (hprimitive : MulAction.IsPreprimitive J (Fin n)) :
    MarkedC4.genRank J ≤ sharpFloor n ∨
      (n = 16 ∧ Nonempty (PrimitiveAffineProfile J (Fin n))) ∨
      ∃ D : NonaffineData J (Fin n), ∃ j : CFSG.Index,
        RemainingModel j ∧ Nonempty (D.Simple ≃* j.Model) := by
  by_cases hlarge : 11 ≤ n
  · exact _root_.SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.PrimitiveBoundedSharpElevenToTwentyOneCFSGReduction.genRank_le_sharpFloor_or_actual_residual
      hclass n hlarge hhi J hprimitive
  have hsmall : n ≤ 10 := by omega
  by_cases h4 : n = 4
  · subst n
    exact Or.inl ((SmallFourPointOrdinaryGenerators.subgroup_genRank_le_two J).trans
      two_le_sharpFloor_four)
  letI : Nontrivial (Fin n) := Finite.one_lt_card_iff_nontrivial.mp
    (by simpa only [Nat.card_fin] using (show 1 < n by omega))
  letI : MulAction.IsPreprimitive J (Fin n) := hprimitive
  obtain ⟨P⟩ := publishedONanScottStructure J (Fin n)
  cases P with
  | inr P =>
      obtain ⟨d,hd⟩ := P.degree_eq_prime_power (⟨0,by omega⟩ : Fin n)
      rcases prime_power_band P.p d n P.p_prime hd hlo hhi with hp | hfour | h8 | h9 | h16
      · exact Or.inl ((PrimitiveAffinePrimeOrdinaryGenerators.genRank_le_two P hprimitive hp).trans
          (two_le_sharpFloor_of_band n hlo hhi))
      · exact (h4 hfour).elim
      · subst n
        have hr := P.subnormal_genRank_le_three_of_degreeEight hprimitive (0 : Fin 8)
          (by simp only [Nat.card_fin]) ⊤ (by exact Subgroup.Normal.isSubnormal inferInstance)
        have he := CoprimeNilpotentProductGenerators.genRank_mulEquiv
          (Subgroup.topEquiv : (⊤ : Subgroup J) ≃* J)
        rw [he] at hr
        have hf : 3 ≤ sharpFloor 8 :=
          TinyPrimeTopSharpFloorNumerics.le_sharpFloor_of_square 8 3 3 (by decide)
            (TinyPrimeTopSharpFloorNumerics.log_le_of_pow 8 3 (by decide) (by decide)) (by decide)
        exact Or.inl (hr.trans hf)
      · subst n
        have hg := PrimitiveAffineNineOrdinaryGenerators.genRank_le_sharpFloor P hprimitive
          (by simp only [Nat.card_fin])
        exact Or.inl (by simpa only [Nat.card_fin] using hg)
      · omega
  | inl D =>
      by_cases h5 : n = 5
      · subst n
        rcases _root_.SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.NaturalDegreeFiveSocleOrdinaryGenerators.genRank_le_sharpFloor_or_actual_remaining_model
          J D hclass with hg | ⟨j,hj,e⟩
        · exact Or.inl hg
        · exact Or.inr (Or.inr ⟨D,j,hj,e⟩)
      · have hlow : 6 ≤ Nat.card (Fin n) := by simpa only [Nat.card_fin] using (show 6 ≤ n by omega)
        have hhigh : Nat.card (Fin n) ≤ 10 := by simpa only [Nat.card_fin] using hsmall
        rcases _root_.SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.PrimitiveSocleSixToTenSharpCFSGReduction.genRank_le_sharpFloor_or_actual_remaining_model
          D hclass hlow hhigh with hg | ⟨j,hj,e⟩
        · exact Or.inl (by simpa only [Nat.card_fin] using hg)
        · exact Or.inr (Or.inr ⟨D,j,hj,e⟩)
end SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.PrimitiveBoundedSharpCFSGReduction

namespace SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.EightPointHalfDegreeFiniteModelReduction
open _root_.SymmetricSubgroupAsymptotics.EightPointHalfDegreeFiniteModelReduction
open PrimitiveSocleRawStructure PermutationOrdinarySmallerActions
open PrimitiveSocleLargeOneFactorOrdinaryCFSGReduction


private theorem half_degree_of_imprimitive_small (n : ℕ) (hn : 4 ≤ n) (hsmall : n ≤ 8)
    (J : Subgroup (Equiv.Perm (Fin n))) (ht : MulAction.IsPretransitive J (Fin n))
    (hp : ¬ MulAction.IsPreprimitive J (Fin n))
    (hbelow : ∀ k : ℕ, k < n → ∀ L : Subgroup (Equiv.Perm (Fin k)),
      (k = 3 → L ≠ ⊤) → ∃ S : Finset L, Subgroup.closure (S : Set L) = ⊤ ∧ 2*S.card ≤ k) :
    2*MarkedC4.genRank J ≤ n := by
  letI : MulAction.IsPretransitive J (Fin n) := ht
  letI : Nontrivial (Fin n) := Finite.one_lt_card_iff_nontrivial.mp
    (by simpa only [Nat.card_fin] using (show 1 < n by omega))
  let x : Fin n := ⟨0,by omega⟩
  obtain ⟨block⟩ := originalMinimalBlock_nonempty (A := J) x hp
  letI : Fintype block.Points := Fintype.ofFinite _
  have hprod := block.degree_product
  simp only [Nat.card_fin] at hprod
  obtain ⟨hr,htop⟩ := block.degrees_ge_two
  have hr4 : Nat.card block.Fibre ≤ 4 := by nlinarith only [hprod,htop,hsmall]
  have hcases : Nat.card block.Fibre = 2 ∨ Nat.card block.Fibre = 3 ∨
      Nat.card block.Fibre = 4 := by omega
  have hrel : Nat.card block.Fibre = (MulAction.stabilizer J x).relIndex block.subgroup :=
    originalTransitiveBlockFibre_card x block.subgroup block.covers.le
  rcases hcases with h2 | h3 | h4
  · let pair : TransitiveBinaryPairCover J x :=
      ⟨block.subgroup,block.covers,hrel.symm.trans h2⟩
    obtain ⟨S,hgen,hcard⟩ := BinaryBlockOrdinaryGeneratorInduction.subgroup_half_degree_generators
      n J ht x pair block.proper hbelow
    exact (Nat.mul_le_mul_left 2 (MarkedC4.genRank_le hgen)).trans hcard
  · obtain ⟨S,hgen,hcard⟩ := TernaryBlockOrdinaryGeneratorInduction.subgroup_half_degree_generators
      n J ht x block.subgroup block.covers.le block.proper (hrel.symm.trans h3) hbelow
    exact (Nat.mul_le_mul_left 2 (MarkedC4.genRank_le hgen)).trans hcard
  · obtain ⟨S,hgen,hcard⟩ := FourPointBlockOrdinaryGeneratorInduction.subgroup_half_degree_generators
      n J x block h4 hbelow
    exact (Nat.mul_le_mul_left 2 (MarkedC4.genRank_le hgen)).trans hcard

theorem exists_minimal_primitive_sporadic_counterexample
    (hclass : CFSGCatalogueWithAxiomMonster.Classification) (n : ℕ) (hn : n ≤ 8)
    (J : Subgroup (Equiv.Perm (Fin n))) (hthree : n = 3 → J ≠ ⊤)
    (hbad : n < 2*MarkedC4.genRank J) :
    Nonempty (PrimitiveSporadicCounterexample n) := by
  let bad : ℕ → Prop := fun k => ∃ L : Subgroup (Equiv.Perm (Fin k)),
    (k = 3 → L ≠ ⊤) ∧ k < 2*MarkedC4.genRank L
  have hex : ∃ k, bad k := ⟨n,J,hthree,hbad⟩
  let m := Nat.find hex
  have hmBad : bad m := Nat.find_spec hex
  obtain ⟨K,hKthree,hKbad⟩ := hmBad
  change m < 2*MarkedC4.genRank K at hKbad
  have hmn : m ≤ n := Nat.find_min' hex ⟨J,hthree,hbad⟩
  have hm8 : m ≤ 8 := hmn.trans hn
  have hmin : ∀ k : ℕ, k < m → ∀ L : Subgroup (Equiv.Perm (Fin k)),
      (k = 3 → L ≠ ⊤) → 2*MarkedC4.genRank L ≤ k := by
    intro k hk L hL
    by_contra hh
    exact Nat.find_min hex hk ⟨L,hL,lt_of_not_ge hh⟩
  have hm4 : 4 ≤ m := by
    by_contra hh
    have hb := PermutationSmallDegreeOrdinaryGenerators.two_mul_genRank_le_degree
      m K (by omega) hKthree
    exact (not_lt_of_ge hb) hKbad
  have hbelow : ∀ k : ℕ, k < m → ∀ L : Subgroup (Equiv.Perm (Fin k)),
      (k = 3 → L ≠ ⊤) → ∃ S : Finset L, Subgroup.closure (S : Set L) = ⊤ ∧ 2*S.card ≤ k := by
    intro k hk L hL
    obtain ⟨S,hcard,hgen⟩ := MarkedC4.genRank_spec (G := L)
    exact ⟨S,hgen,by rw [hcard]; exact hmin k hk L hL⟩
  have hb : SmallerActionBound (Nat.card (Fin m)) := by
    simpa only [Nat.card_fin] using smallerActionBound_of_subgroup_generators m hbelow
  have ht : MulAction.IsPretransitive K (Fin m) := by
    by_contra hh
    have hhalf := IntransitiveOrdinaryGeneratorInduction.half_degree_of_intransitive hh hb
    simp only [Nat.card_fin] at hhalf
    exact (not_lt_of_ge hhalf) hKbad
  have hp : MulAction.IsPreprimitive K (Fin m) := by
    by_contra hh
    have hhalf := half_degree_of_imprimitive_small m hm4 hm8 K ht hh hbelow
    exact (not_lt_of_ge hhalf) hKbad
  rcases _root_.SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.PrimitiveBoundedSharpCFSGReduction.genRank_le_sharpFloor_or_actual_residual
    hclass m hm4 (by omega) K hp with hpaid | haffine | ⟨D,j,hj,⟨e⟩⟩
  · have hh := hpaid.trans (TraceySharpHalfDegreeNumerics.sharpFloor_le_half m hm4)
    have hhalf := (Nat.mul_le_mul_left 2 hh).trans (Nat.mul_div_le m 2)
    exact ((not_lt_of_ge hhalf) hKbad).elim
  · have hh := haffine.1
    omega
  · cases j <;> try exact hj.elim
    case tits =>
      exact (PrimitiveSocleEightPointTitsExclusion.not_tits_of_degree_le_eight D
        (by simpa only [Nat.card_fin] using hm8) e).elim
    case sporadic s =>
      exact ⟨⟨m,hm4,hmn,K,ht,hp,hKbad,hmin,D,s,e⟩⟩

theorem half_degree_or_sporadic_counterexample
    (hclass : CFSGCatalogueWithAxiomMonster.Classification) (n : ℕ) (hn : n ≤ 8)
    (J : Subgroup (Equiv.Perm (Fin n))) (hthree : n = 3 → J ≠ ⊤) :
    2*MarkedC4.genRank J ≤ n ∨ Nonempty (PrimitiveSporadicCounterexample n) := by
  by_cases hh : 2*MarkedC4.genRank J ≤ n
  · exact Or.inl hh
  · exact Or.inr (exists_minimal_primitive_sporadic_counterexample hclass n hn J hthree
      (lt_of_not_ge hh))

theorem genRank_le_four_or_sporadic_counterexample
    (hclass : CFSGCatalogueWithAxiomMonster.Classification) (J : Subgroup (Equiv.Perm (Fin 8))) :
    MarkedC4.genRank J ≤ 4 ∨ Nonempty (PrimitiveSporadicCounterexample 8) := by
  rcases half_degree_or_sporadic_counterexample hclass 8 (by decide) J (by omega) with hh | hr
  · exact Or.inl (by omega)
  · exact Or.inr hr
end SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.EightPointHalfDegreeFiniteModelReduction

namespace SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.NinePointHalfDegreeCompleteCFSG
open _root_.SymmetricSubgroupAsymptotics.NinePointHalfDegreeCompleteCFSG
theorem genRank_le_four (hclass : CFSGCatalogueWithAxiomMonster.Classification)
    (J : Subgroup (Equiv.Perm (Fin 9))) : MarkedC4.genRank J≤4 := by
  have hbelow : ∀ k : ℕ,k<9→∀L : Subgroup (Equiv.Perm (Fin k)),
      (k=3→L≠⊤)→∃S : Finset L,Subgroup.closure (S : Set L)=⊤ ∧ 2*S.card≤k := by
    intro k hk L hthree
    rcases _root_.SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.EightPointHalfDegreeFiniteModelReduction.half_degree_or_sporadic_counterexample
      hclass k (by omega) L hthree with hpaid | hbad
    · obtain ⟨S,hcard,hgen⟩ := MarkedC4.genRank_spec (G := L)
      exact ⟨S,hgen,by rw [hcard]; exact hpaid⟩
    · exact (_root_.SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.EightPointHalfDegreeCompleteCFSG.no_primitive_sporadic_counterexample_eight
        hclass (_root_.SymmetricSubgroupAsymptotics.EightPointFaithfulActionHalfDegreeReduction.counterexample_mono (by omega) hbad)).elim
  by_cases ht : MulAction.IsPretransitive J (Fin 9)
  swap
  · obtain ⟨S,hgen,hcard⟩ :=
      IntransitiveOrdinaryGeneratorInduction.subgroup_half_degree_generators 9 J ht hbelow
    have hr := MarkedC4.genRank_le hgen
    omega
  by_cases hp : MulAction.IsPreprimitive J (Fin 9)
  · exact PrimitiveNineOrdinaryGeneratorsWithoutClassification.genRank_le_four J hp
  letI : MulAction.IsPretransitive J (Fin 9) := ht
  let x : Fin 9 := 0
  obtain ⟨block⟩ := originalMinimalBlock_nonempty (A := J) x hp
  have hprod := block.degree_product
  simp only [Nat.card_fin] at hprod
  obtain ⟨hr,htop⟩ := block.degrees_ge_two
  have hdiv : Nat.card block.Fibre ∣ 9 := ⟨Nat.card block.Points,hprod.symm⟩
  have hlt : Nat.card block.Fibre<9 := by nlinarith
  have hthree : Nat.card block.Fibre=3 := by
    have hmenu : ∀ i : Fin 9, 2 ≤ i.val → i.val ∣ 9 → i.val = 3 := by decide +kernel
    exact hmenu ⟨Nat.card block.Fibre,hlt⟩ hr hdiv
  have hrel : Nat.card block.Fibre=(MulAction.stabilizer J x).relIndex block.subgroup :=
    originalTransitiveBlockFibre_card x block.subgroup block.covers.le
  obtain ⟨S,hgen,hcard⟩ := TernaryBlockOrdinaryGeneratorInduction.subgroup_half_degree_generators
    9 J ht x block.subgroup block.covers.le block.proper (hrel.symm.trans hthree) hbelow
  have hbound := MarkedC4.genRank_le hgen
  omega

 theorem genRank_le_four_of_faithful {G X : Type} [Group G] [Finite G] [Finite X]
    [MulAction G X] [FaithfulSMul G X] (hclass : CFSGCatalogueWithAxiomMonster.Classification)
    (hdegree : Nat.card X=9) : MarkedC4.genRank G≤4 := by
  let points : X ≃ Fin 9 := Finite.equivFinOfCardEq hdegree
  exact (CoprimeNilpotentProductGenerators.genRank_mulEquiv (faithfulLabelledActionEquiv points)).le.trans
    (genRank_le_four hclass (labelledActionImage (A := G) points))
end SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.NinePointHalfDegreeCompleteCFSG

namespace SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.PrimitiveTenOrdinaryGeneratorsFromNineCFSG
open _root_.SymmetricSubgroupAsymptotics.PrimitiveTenOrdinaryGeneratorsFromNineCFSG
theorem genRank_le_five (hclass : CFSGCatalogueWithAxiomMonster.Classification)
    (J : Subgroup (Equiv.Perm (Fin 10))) (hp : MulAction.IsPreprimitive J (Fin 10)) :
    MarkedC4.genRank J≤5 := by
  letI : MulAction.IsPreprimitive J (Fin 10) := hp
  let x : Fin 10 := 0
  let H := MulAction.stabilizer J x
  let Y := SubMulAction.ofStabilizer J x
  letI : FaithfulSMul H Y := PointStabilizerComplementFaithful.faithfulSMul J (Fin 10) x
  have hY : Nat.card Y=9 := by
    simpa only [Nat.card_fin] using SubMulAction.nat_card_ofStabilizer_eq J x
  have hr := _root_.SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.NinePointHalfDegreeCompleteCFSG.genRank_le_four_of_faithful (G := H) (X := Y) hclass hY
  have hcoat : IsCoatom H := (MulAction.isCoatom_stabilizer_iff_preprimitive J x).mpr hp
  have hJ := MaximalSubgroupOrdinaryGenerators.genRank_le_add_one H hcoat
  omega
end SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.PrimitiveTenOrdinaryGeneratorsFromNineCFSG

namespace SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.TenPointMinimalFailureDegreeNineOrTen
open _root_.SymmetricSubgroupAsymptotics.TenPointMinimalFailureDegreeNineOrTen
open _root_.SymmetricSubgroupAsymptotics.EightPointHalfDegreeFiniteModelReduction

theorem degree_eq_nine_or_ten (hclass : CFSGCatalogueWithAxiomMonster.Classification)
    (w : PrimitiveSporadicCounterexample 10) : w.degree=9 ∨ w.degree=10 := by
  by_cases h8 : w.degree≤8
  · apply (_root_.SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.EightPointHalfDegreeCompleteCFSG.no_primitive_sporadic_counterexample_eight hclass ?_).elim
    exact ⟨⟨w.degree,w.degree_ge_four,h8,w.group,w.transitive,w.primitive,
      w.failed,w.minimal,w.socle,w.sporadic,w.equiv⟩⟩
  · have hhi := w.degree_le
    omega
end SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.TenPointMinimalFailureDegreeNineOrTen

namespace SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.TenPointGlobalCounterexampleCompleteCFSG
open _root_.SymmetricSubgroupAsymptotics.TenPointGlobalCounterexampleCompleteCFSG
open _root_.SymmetricSubgroupAsymptotics.EightPointHalfDegreeFiniteModelReduction

 theorem no_primitive_sporadic_counterexample_ten (hclass : CFSGCatalogueWithAxiomMonster.Classification) :
    ¬Nonempty (PrimitiveSporadicCounterexample 10) := by
  rintro ⟨w⟩
  have hd := _root_.SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.TenPointMinimalFailureDegreeNineOrTen.degree_eq_nine_or_ten hclass w
  rcases w with ⟨d,hlo,hhi,J,ht,hp,hbad,hmin,D,s,e⟩
  change d=9 ∨ d=10 at hd
  rcases hd with h9 | h10
  · subst d
    have hr := PrimitiveNineOrdinaryGeneratorsWithoutClassification.genRank_le_four J hp
    omega
  · subst d
    have hr := _root_.SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.PrimitiveTenOrdinaryGeneratorsFromNineCFSG.genRank_le_five hclass J hp
    omega

 theorem no_cumulative_global_counterexample_ten (hclass : CFSGCatalogueWithAxiomMonster.Classification) :
    ¬Nonempty (_root_.SymmetricSubgroupAsymptotics.OriginalAffineBoundedSharpCoTwoTopRefinement.CumulativeGlobalCounterexample 10) := by
  rintro ⟨w⟩
  exact no_primitive_sporadic_counterexample_ten hclass ⟨w.val⟩
end SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.TenPointGlobalCounterexampleCompleteCFSG

namespace SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.TenPointHalfDegreeFiniteModelReduction
open _root_.SymmetricSubgroupAsymptotics.TenPointHalfDegreeFiniteModelReduction
open PrimitiveSocleRawStructure PermutationOrdinarySmallerActions
open PrimitiveSocleLargeOneFactorOrdinaryCFSGReduction
open _root_.SymmetricSubgroupAsymptotics.EightPointHalfDegreeFiniteModelReduction

private theorem half_degree_of_imprimitive_small (n : ℕ) (hn : 4 ≤ n) (hsmall : n ≤ 10)
    (J : Subgroup (Equiv.Perm (Fin n))) (ht : MulAction.IsPretransitive J (Fin n))
    (hp : ¬ MulAction.IsPreprimitive J (Fin n))
    (hbelow : ∀ k : ℕ, k < n → ∀ L : Subgroup (Equiv.Perm (Fin k)),
      (k = 3 → L ≠ ⊤) → ∃ S : Finset L, Subgroup.closure (S : Set L) = ⊤ ∧ 2*S.card ≤ k) :
    2*MarkedC4.genRank J ≤ n := by
  letI : MulAction.IsPretransitive J (Fin n) := ht
  letI : Nontrivial (Fin n) := Finite.one_lt_card_iff_nontrivial.mp
    (by simpa only [Nat.card_fin] using (show 1 < n by omega))
  let x : Fin n := ⟨0,by omega⟩
  obtain ⟨block⟩ := originalMinimalBlock_nonempty (A := J) x hp
  letI : Fintype block.Points := Fintype.ofFinite _
  have hprod := block.degree_product
  simp only [Nat.card_fin] at hprod
  obtain ⟨hr,htop⟩ := block.degrees_ge_two
  have hr5 : Nat.card block.Fibre ≤ 5 := by nlinarith only [hprod,htop,hsmall]
  have hcases : Nat.card block.Fibre = 2 ∨ Nat.card block.Fibre = 3 ∨
      Nat.card block.Fibre = 4 ∨ Nat.card block.Fibre = 5 := by omega
  have hrel : Nat.card block.Fibre = (MulAction.stabilizer J x).relIndex block.subgroup :=
    originalTransitiveBlockFibre_card x block.subgroup block.covers.le
  rcases hcases with h2 | h3 | h4 | h5
  · let pair : TransitiveBinaryPairCover J x :=
      ⟨block.subgroup,block.covers,hrel.symm.trans h2⟩
    obtain ⟨S,hgen,hcard⟩ := BinaryBlockOrdinaryGeneratorInduction.subgroup_half_degree_generators
      n J ht x pair block.proper hbelow
    exact (Nat.mul_le_mul_left 2 (MarkedC4.genRank_le hgen)).trans hcard
  · obtain ⟨S,hgen,hcard⟩ := TernaryBlockOrdinaryGeneratorInduction.subgroup_half_degree_generators
      n J ht x block.subgroup block.covers.le block.proper (hrel.symm.trans h3) hbelow
    exact (Nat.mul_le_mul_left 2 (MarkedC4.genRank_le hgen)).trans hcard
  · obtain ⟨S,hgen,hcard⟩ := FourPointBlockOrdinaryGeneratorInduction.subgroup_half_degree_generators
      n J x block h4 hbelow
    exact (Nat.mul_le_mul_left 2 (MarkedC4.genRank_le hgen)).trans hcard
  · have hb : SmallerActionBound (Nat.card (Fin n)) := by
      simpa only [Nat.card_fin] using smallerActionBound_of_subgroup_generators n hbelow
    have hthree : Nat.card block.Points ≠ 3 := by rw [h5] at hprod; omega
    have hh := OddBlockOrdinaryGeneratorInduction.half_degree_of_odd_fibres
      block.map block.map_equivariant block.base (by rw [h5]; decide)
      (by change 5 ≤ Nat.card block.Fibre; omega) block.degrees_ge_two.2 hthree hb
    simpa only [Nat.card_fin] using hh

theorem exists_minimal_primitive_sporadic_counterexample
    (hclass : CFSGCatalogueWithAxiomMonster.Classification) (n : ℕ) (hn : n ≤ 10)
    (J : Subgroup (Equiv.Perm (Fin n))) (hthree : n = 3 → J ≠ ⊤)
    (hbad : n < 2*MarkedC4.genRank J) :
    Nonempty (PrimitiveSporadicCounterexample n) := by
  let bad : ℕ → Prop := fun k => ∃ L : Subgroup (Equiv.Perm (Fin k)),
    (k = 3 → L ≠ ⊤) ∧ k < 2*MarkedC4.genRank L
  have hex : ∃ k, bad k := ⟨n,J,hthree,hbad⟩
  let m := Nat.find hex
  have hmBad : bad m := Nat.find_spec hex
  obtain ⟨K,hKthree,hKbad⟩ := hmBad
  change m < 2*MarkedC4.genRank K at hKbad
  have hmn : m ≤ n := Nat.find_min' hex ⟨J,hthree,hbad⟩
  have hm10 : m ≤ 10 := hmn.trans hn
  have hmin : ∀ k : ℕ, k < m → ∀ L : Subgroup (Equiv.Perm (Fin k)),
      (k = 3 → L ≠ ⊤) → 2*MarkedC4.genRank L ≤ k := by
    intro k hk L hL
    by_contra hh
    exact Nat.find_min hex hk ⟨L,hL,lt_of_not_ge hh⟩
  have hm4 : 4 ≤ m := by
    by_contra hh
    have hb := PermutationSmallDegreeOrdinaryGenerators.two_mul_genRank_le_degree
      m K (by omega) hKthree
    exact (not_lt_of_ge hb) hKbad
  have hbelow : ∀ k : ℕ, k < m → ∀ L : Subgroup (Equiv.Perm (Fin k)),
      (k = 3 → L ≠ ⊤) → ∃ S : Finset L, Subgroup.closure (S : Set L) = ⊤ ∧ 2*S.card ≤ k := by
    intro k hk L hL
    obtain ⟨S,hcard,hgen⟩ := MarkedC4.genRank_spec (G := L)
    exact ⟨S,hgen,by rw [hcard]; exact hmin k hk L hL⟩
  have hb : SmallerActionBound (Nat.card (Fin m)) := by
    simpa only [Nat.card_fin] using smallerActionBound_of_subgroup_generators m hbelow
  have ht : MulAction.IsPretransitive K (Fin m) := by
    by_contra hh
    have hhalf := IntransitiveOrdinaryGeneratorInduction.half_degree_of_intransitive hh hb
    simp only [Nat.card_fin] at hhalf
    exact (not_lt_of_ge hhalf) hKbad
  have hp : MulAction.IsPreprimitive K (Fin m) := by
    by_contra hh
    have hhalf := half_degree_of_imprimitive_small m hm4 hm10 K ht hh hbelow
    exact (not_lt_of_ge hhalf) hKbad
  rcases _root_.SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.PrimitiveBoundedSharpCFSGReduction.genRank_le_sharpFloor_or_actual_residual
    hclass m hm4 (by omega) K hp with hpaid | haffine | ⟨D,j,hj,⟨e⟩⟩
  · have hh := hpaid.trans (TraceySharpHalfDegreeNumerics.sharpFloor_le_half m hm4)
    have hhalf := (Nat.mul_le_mul_left 2 hh).trans (Nat.mul_div_le m 2)
    exact ((not_lt_of_ge hhalf) hKbad).elim
  · have hh := haffine.1
    omega
  · cases j <;> try exact hj.elim
    case tits =>
      exact (PrimitiveSocleElevenPointTitsExclusion.not_tits_of_degree_le_eleven D
        (by simpa only [Nat.card_fin] using (show m ≤ 11 by omega)) e).elim
    case sporadic s =>
      exact ⟨⟨m,hm4,hmn,K,ht,hp,hKbad,hmin,D,s,e⟩⟩

theorem half_degree_or_sporadic_counterexample
    (hclass : CFSGCatalogueWithAxiomMonster.Classification) (n : ℕ) (hn : n ≤ 10)
    (J : Subgroup (Equiv.Perm (Fin n))) (hthree : n = 3 → J ≠ ⊤) :
    2*MarkedC4.genRank J ≤ n ∨ Nonempty (PrimitiveSporadicCounterexample n) := by
  by_cases hh : 2*MarkedC4.genRank J ≤ n
  · exact Or.inl hh
  · exact Or.inr (exists_minimal_primitive_sporadic_counterexample hclass n hn J hthree
      (lt_of_not_ge hh))

theorem two_mul_genRank_le_card_or_sporadic_counterexample
    (hclass : CFSGCatalogueWithAxiomMonster.Classification) {G X : Type}
    [Group G] [Finite G] [Finite X] [MulAction G X] [FaithfulSMul G X]
    (hsmall : Nat.card X ≤ 10) (hthree : Nat.card X ≠ 3) :
    2*MarkedC4.genRank G ≤ Nat.card X ∨
      Nonempty (PrimitiveSporadicCounterexample 10) := by
  let e : X ≃ Fin (Nat.card X) := Finite.equivFinOfCardEq rfl
  let rho : G →* Equiv.Perm (Fin (Nat.card X)) :=
    e.permCongrHom.toMonoidHom.comp (MulAction.toPermHom G X)
  have hrho : Function.Injective rho :=
    e.permCongrHom.injective.comp MulAction.toPerm_injective
  let f : G ≃* rho.range := MonoidHom.ofInjective hrho
  rcases half_degree_or_sporadic_counterexample hclass (Nat.card X) hsmall
    rho.range (fun h => (hthree h).elim) with hpaid | hbad
  · exact Or.inl (by
      simpa only [← CoprimeNilpotentProductGenerators.genRank_mulEquiv f] using hpaid)
  · exact Or.inr (_root_.SymmetricSubgroupAsymptotics.EightPointFaithfulActionHalfDegreeReduction.counterexample_mono hsmall hbad)
end SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.TenPointHalfDegreeFiniteModelReduction

namespace SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.TenPointHalfDegreeCompleteCFSG
open _root_.SymmetricSubgroupAsymptotics.TenPointHalfDegreeCompleteCFSG
theorem subgroup_half_degree (hclass : CFSGCatalogueWithAxiomMonster.Classification) (n : ℕ) (hn : n ≤ 10)
    (J : Subgroup (Equiv.Perm (Fin n))) (hthree : n=3 → J≠⊤) :
    2*MarkedC4.genRank J ≤ n := by
  rcases _root_.SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.TenPointHalfDegreeFiniteModelReduction.half_degree_or_sporadic_counterexample
    hclass n hn J hthree with hpaid | hbad
  · exact hpaid
  · exact (_root_.SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.TenPointGlobalCounterexampleCompleteCFSG.no_primitive_sporadic_counterexample_ten
      hclass (_root_.SymmetricSubgroupAsymptotics.EightPointFaithfulActionHalfDegreeReduction.counterexample_mono hn hbad)).elim

theorem subgroup_genRank_le_fixedBudget (hclass : CFSGCatalogueWithAxiomMonster.Classification)
    (n : ℕ) (hn : n ≤ 10) (J : Subgroup (Equiv.Perm (Fin n))) :
    MarkedC4.genRank J ≤ fixedBudget n := by
  by_cases h3 : n=3
  · subst n
    have hc : Nat.card J ≤ 6 := by
      simpa only [Nat.card_perm,Nat.card_fin] using
        Nat.card_le_card_of_injective (Subtype.val : J → Equiv.Perm (Fin 3))
          Subtype.val_injective
    have hr : MarkedC4.genRank J ≤ 2 := by
      by_contra hh
      have hp := (Nat.pow_le_pow_right (by decide : 0 < 2)
        (show 3 ≤ MarkedC4.genRank J by omega)).trans
        ((FiniteGroupBinaryOrderGenerators.two_pow_genRank_le_card J).trans hc)
      norm_num at hp
    simpa only [fixedBudget,if_pos rfl] using hr
  · have hh := subgroup_half_degree hclass n hn J (fun h => (h3 h).elim)
    have hr : MarkedC4.genRank J ≤ n/2 := by omega
    simpa only [fixedBudget,if_neg h3] using hr

theorem faithful_genRank_le_fixedBudget (hclass : CFSGCatalogueWithAxiomMonster.Classification)
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X] [FaithfulSMul G X]
    (hsmall : Nat.card X ≤ 10) : MarkedC4.genRank G ≤ fixedBudget (Nat.card X) := by
  let points : X ≃ Fin (Nat.card X) := Finite.equivFinOfCardEq rfl
  exact (CoprimeNilpotentProductGenerators.genRank_mulEquiv
    (faithfulLabelledActionEquiv points)).le.trans
    (subgroup_genRank_le_fixedBudget hclass (Nat.card X) hsmall
      (labelledActionImage (A := G) points))
end SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.TenPointHalfDegreeCompleteCFSG
