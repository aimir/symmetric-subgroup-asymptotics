import SymmetricSubgroupAsymptotics.CFSGSufficientPrimitiveSocleQuotient
import SymmetricSubgroupAsymptotics.PrimitiveDegreeEightRoundingQuotient
import SymmetricSubgroupAsymptotics.PrimitiveDegreeNineQuotientPointTransport
import SymmetricSubgroupAsymptotics.PrimitiveDegreeSevenElevenRoundingCompression

/-! The retained sharp bound below27 suffices for the actual eight/nine/
eleven-point quotient margins. The existing actual eight-point literal
coverage and point-coordinate equivalences are used unchanged. -/

/-! The retained actual eight-point classification supplies only the
small quotient margin required for compression. The three affine entries
are excluded by the actual simple full socle, and no C336 row is used. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical IsMulCommutative
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [Nontrivial X] [MulAction.IsPreprimitive G X]

private theorem quotient_le_seven_of_order
    (D : NonaffineData G X) (hk : D.factorCount=1)
    (hindex : SufficientSimpleIndexBounds) (hX : Nat.card X=8)
    (hG : Nat.card G=168 ∨ Nat.card G=336) :
    Nat.card (G⧸finiteGroupSocle G)≤7 := by
  obtain ⟨ell,_,hf,he,hlog⟩ := D.oneFactor_sharp_log_of_sufficient_degree_lt_twentySeven hk hindex (by first | omega | simp)
  have hpow : 2^Nat.card (G⧸finiteGroupSocle G)≤512 := by
    have hp := quotientOrder_twoPow_le_cube_of_log (by omega) hlog
    have he8 : ell≤8 := by omega
    exact hp.trans (by simpa using Nat.pow_le_pow_left he8 3)
  have hq9 : Nat.card (G⧸finiteGroupSocle G)≤9 := by
    by_contra h
    have hh : 1024≤512 := calc
      1024=2^10 := by decide
      _ ≤ 2^Nat.card (G⧸finiteGroupSocle G) :=
        pow_le_pow_right₀ (by decide : 1≤(2 : ℕ)) (by omega)
      _ ≤ 512 := hpow
    omega
  letI : MulAction.IsPretransitive (finiteGroupSocle G) X := D.socle_transitive
  have hd : 8∣Nat.card (finiteGroupSocle G) := by
    simpa only [hX] using degree_dvd_card_of_transitive_normal
      (X := X) (finiteGroupSocle G)
  have hm := (Subgroup.card_eq_card_quotient_mul_card_subgroup (finiteGroupSocle G)).symm
  by_contra hn
  have hq : Nat.card (G⧸finiteGroupSocle G)=8 ∨
      Nat.card (G⧸finiteGroupSocle G)=9 := by omega
  obtain ⟨k,hk⟩ := hd
  rcases hq with hq|hq
  all_goals rw [hq] at hm
  all_goals rcases hG with hG|hG
  all_goals omega

private theorem from_literal
    (D : NonaffineData G X) (hk : D.factorCount=1)
    (hindex : SufficientSimpleIndexBounds) (hX : Nat.card X=8)
    (j : Fin 24) (hj : 17≤j.val)
    (e : G≃*(DegreeTwoPairedEightSharedTops.interface j).top) :
    Nat.card (G⧸finiteGroupSocle G)≤7 := by
  fin_cases j
  all_goals try norm_num at hj
  · exact (D.oneFactor_not_affineModel hk (by decide)
      PrimitiveAffineDegreeTwoPairedEightAffineTops.Row18.linearGroup
      (e.trans PrimitiveAffineDegreeTwoPairedEightAffineTops.Row18.modelEquiv)).elim
  · exact (D.oneFactor_not_affineModel hk (by decide)
      PrimitiveAffineDegreeTwoPairedEightRow19AffineTop.linearGroup
      (e.trans PrimitiveAffineDegreeTwoPairedEightRow19AffineTop.modelEquiv)).elim
  · exact (D.oneFactor_not_affineModel hk (by decide)
      PrimitiveAffineDegreeTwoPairedEightAffineTops.Row20.linearGroup
      (e.trans PrimitiveAffineDegreeTwoPairedEightAffineTops.Row20.modelEquiv)).elim
  · letI : Group PrimitiveAffineEightFrameRow28TopCertificate.Source :=
      PrimitiveAffineEightFrameRow28TopCertificate.group
    have ht : Nat.card (DegreeTwoPairedEightSharedTops.interface (20 : Fin 24)).top=168 := by
      change Nat.card (Subgroup.closure (Set.range PrimitiveAffineEightFrameRow28TopCertificate.generators))=168
      rw [←Nat.card_congr PrimitiveAffineEightFrameRow28TopCertificate.originalEquiv.toEquiv]
      exact PrimitiveAffineEightFrameRow28TopCertificate.source_card
    exact quotient_le_seven_of_order D hk hindex hX
      (Or.inl ((Nat.card_congr e.toEquiv).trans ht))
  · letI : Group PrimitiveAffineEightFrameRow29TopCertificate.Source :=
      PrimitiveAffineEightFrameRow29TopCertificate.group
    have ht : Nat.card (DegreeTwoPairedEightSharedTops.interface (21 : Fin 24)).top=336 := by
      change Nat.card (Subgroup.closure (Set.range PrimitiveAffineEightFrameRow29TopCertificate.generators))=336
      rw [←Nat.card_congr PrimitiveAffineEightFrameRow29TopCertificate.originalEquiv.toEquiv]
      exact PrimitiveAffineEightFrameRow29TopCertificate.source_card
    exact quotient_le_seven_of_order D hk hindex hX
      (Or.inr ((Nat.card_congr e.toEquiv).trans ht))
  · let eA : G≃*alternatingGroup (Fin 8) := e.trans
      (MulEquiv.subgroupCongr DegreeTwoPairedEightSharedTops.top23_eq_alternating)
    exact (quotient_card_le_two_of_alternating_equiv 8 (by decide) eA
      (finiteGroupSocle G) (D.oneFactor_socle_nontrivial hk)).trans (by decide)
  · let eS : G≃*Equiv.Perm (Fin 8) := e.trans
      ((MulEquiv.subgroupCongr DegreeTwoPairedEightSharedTops.top24_eq_top).trans
        Subgroup.topEquiv)
    exact (quotient_card_le_two_of_symmetric_equiv 8 (by decide) eS
      (finiteGroupSocle G) (D.oneFactor_socle_nontrivial hk)).trans (by decide)

theorem NonaffineData.degreeEight_quotient_card_le_seven_of_sufficient
    (D : NonaffineData G X) (hindex : SufficientSimpleIndexBounds)
    (published : DegreeEightCanonicalCatalogue.PublishedClassification)
    (hX : Nat.card X=8) : Nat.card (G⧸finiteGroupSocle G)≤7 := by
  have hk := D.factorCount_one_of_sufficient_degree_lt_twentyFive hindex (by omega)
  let points : X≃Fin 8 := Finite.equivFinOfCardEq hX
  let S := labelledActionImage (A := G) points
  letI : MulAction.IsPreprimitive S (Fin 8) :=
    (labelledAction_preprimitive_iff points).mp inferInstance
  let M := DegreeEightCanonicalCatalogue.primitiveLiteralMatch published S (by simp)
  let e : G≃*(DegreeTwoPairedEightSharedTops.interface M.index).top :=
    (faithfulLabelledActionEquiv points).trans M.groupEquiv
  exact from_literal D hk hindex hX M.index M.primitive_index e

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure


/-! Ordinary retained simple-index bounds and the actual regular Sylow
normalizer exclude the last quotient order nine in degree nine. The actual
socle quotient therefore has order at most eight, without any C336 row. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure

theorem NonaffineData.degreeNine_quotient_card_le_eight_of_sufficient
    {G : Type} [Group G] [Finite G] [MulAction G (Fin 9)]
    [FaithfulSMul G (Fin 9)] (D : NonaffineData G (Fin 9))
    (hindex : SufficientSimpleIndexBounds) :
    Nat.card (G ⧸ finiteGroupSocle G) ≤ 8 := by
  have hk := D.factorCount_one_of_sufficient_degree_lt_twentyFive hindex (by simp)
  obtain ⟨ell,_,hf,he,hlog⟩ := D.oneFactor_sharp_log_of_sufficient_degree_lt_twentySeven hk hindex (by first | omega | simp)
  have hpow := quotientOrder_twoPow_le_cube_of_log (by omega) hlog
  have he' : ell ≤ 9 := by simpa only [Nat.card_fin] using he
  have hcube : 2 ^ Nat.card (G ⧸ finiteGroupSocle G) ≤ 729 :=
    hpow.trans (Nat.pow_le_pow_left he' 3)
  have hten : Nat.card (G ⧸ finiteGroupSocle G) < 10 := by
    by_contra h
    have hlo : 10 ≤ Nat.card (G ⧸ finiteGroupSocle G) := by omega
    have hbad : 1024 ≤ 729 := calc
      1024 = 2 ^ 10 := by decide
      _ ≤ 2 ^ Nat.card (G ⧸ finiteGroupSocle G) :=
        pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) hlo
      _ ≤ 729 := hcube
    omega
  letI : MulAction.IsPretransitive (finiteGroupSocle G) (Fin 9) := D.socle_transitive
  have hne := ninePoint_normal_transitive_quotient_card_ne_nine (finiteGroupSocle G)
  omega

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure


/-! The degree-nine quotient bound on the original finite point type,
needed for actual minimal-block fibres. Only the point coordinates change. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure

theorem NonaffineData.degreeNine_quotient_card_le_eight_of_card_of_sufficient
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] (D : NonaffineData G X) (hX : Nat.card X = 9)
    (hindex : SufficientSimpleIndexBounds) :
    Nat.card (G ⧸ finiteGroupSocle G) ≤ 8 := by
  let e : X ≃ Fin 9 := Finite.equivFinOfCardEq hX
  letI : MulAction G (Fin 9) := MulAction.compHom (Fin 9) (labelledActionHom e)
  letI : FaithfulSMul G (Fin 9) := {
    eq_of_smul_eq_smul := fun {a b} hab =>
      labelledActionHom_injective e (Equiv.Perm.ext hab) }
  let D' : NonaffineData G (Fin 9) := D.transportPoints e
    (fun g x => (labelledActionHom_apply e g x).symm)
  exact D'.degreeNine_quotient_card_le_eight_of_sufficient hindex

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure


/-! The actual degree-seven and degree-eleven semisimple quotients have
strict rounding compression. The boundary orders6 and10 use disjoint
coprime coset actions of degrees5 and7, respectively. No small abstract
group model or primitive correspondence is supplied. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
open OuterWreathPermutationCompression

variable {G : Type} [Group G] [Finite G]

def NonaffineData.degreeSeven_roundingCompression_of_sufficient [MulAction G (Fin 7)]
    [FaithfulSMul G (Fin 7)] (D : NonaffineData G (Fin 7)) :
    LocalSemisimpleRoundingCompressionData G 7 := by
  apply Classical.choice
  have hq := D.degreeSeven_quotient_card_le_six
  by_cases h6 : Nat.card (G ⧸ finiteGroupSocle G) = 6
  · obtain ⟨d,hd,hd6,_,f,hf⟩ :=
      CoprimeCosetPermutationCompression.order_six_or_ten_faithful_action (Or.inl h6)
    exact ⟨{
      E := finiteGroupSocle G
      chart := D.chart
      quotientDegree := d
      quotientDegree_pos := hd
      quotientAction := f
      quotientAction_injective := hf
      degree_bound := by decide
      quotientDegree_gap := by rw [hd6 h6]; decide }⟩
  · exact ⟨{
      E := finiteGroupSocle G
      chart := D.chart
      quotientDegree := Nat.card (G ⧸ finiteGroupSocle G)
      quotientDegree_pos := Nat.card_pos
      quotientAction := regularAction _
      quotientAction_injective := regularAction_injective _
      degree_bound := by decide
      quotientDegree_gap := by
        have he : evenWidth 7 = 6 := by decide
        rw [he]
        omega }⟩

theorem NonaffineData.degreeEleven_quotient_card_le_ten_of_sufficient [MulAction G (Fin 11)]
    (D : NonaffineData G (Fin 11)) (hindex : SufficientSimpleIndexBounds) :
    Nat.card (G ⧸ finiteGroupSocle G) ≤ 10 := by
  have hk := D.factorCount_one_of_sufficient_degree_lt_twentyFive hindex (by simp)
  obtain ⟨ell,_,hf,he,hlog⟩ := D.oneFactor_sharp_log_of_sufficient_degree_lt_twentySeven hk hindex (by first | omega | simp)
  have hpow := quotientOrder_twoPow_le_cube_of_log (by omega) hlog
  have he' : ell ≤ 11 := by simpa only [Nat.card_fin] using he
  have hcube : 2 ^ Nat.card (G ⧸ finiteGroupSocle G) ≤ 1331 :=
    hpow.trans (Nat.pow_le_pow_left he' 3)
  by_contra h
  have hlo : 11 ≤ Nat.card (G ⧸ finiteGroupSocle G) := by omega
  have hbad : 2048 ≤ 1331 := calc
    2048 = 2 ^ 11 := by decide
    _ ≤ 2 ^ Nat.card (G ⧸ finiteGroupSocle G) :=
      pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) hlo
    _ ≤ 1331 := hcube
  omega

def NonaffineData.degreeEleven_roundingCompression_of_sufficient [MulAction G (Fin 11)]
    (D : NonaffineData G (Fin 11)) (hindex : SufficientSimpleIndexBounds) :
    LocalSemisimpleRoundingCompressionData G 11 := by
  apply Classical.choice
  have hq := D.degreeEleven_quotient_card_le_ten_of_sufficient hindex
  by_cases h10 : Nat.card (G ⧸ finiteGroupSocle G) = 10
  · obtain ⟨d,hd,_,hd10,f,hf⟩ :=
      CoprimeCosetPermutationCompression.order_six_or_ten_faithful_action (Or.inr h10)
    exact ⟨{
      E := finiteGroupSocle G
      chart := D.chart
      quotientDegree := d
      quotientDegree_pos := hd
      quotientAction := f
      quotientAction_injective := hf
      degree_bound := by decide
      quotientDegree_gap := by rw [hd10 h10]; decide }⟩
  · exact ⟨{
      E := finiteGroupSocle G
      chart := D.chart
      quotientDegree := Nat.card (G ⧸ finiteGroupSocle G)
      quotientDegree_pos := Nat.card_pos
      quotientAction := regularAction _
      quotientAction_injective := regularAction_injective _
      degree_bound := by decide
      quotientDegree_gap := by
        have he : evenWidth 11 = 10 := by decide
        rw [he]
        omega }⟩

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
