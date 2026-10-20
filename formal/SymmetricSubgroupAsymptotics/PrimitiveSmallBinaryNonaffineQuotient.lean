import SymmetricSubgroupAsymptotics.PrimitiveSimpleSocleExcludesSolubleNormal
import SymmetricSubgroupAsymptotics.PrimitiveNaturalSocleQuotient
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenCanonicalCatalogue
import SymmetricSubgroupAsymptotics.PrimitiveEightCanonicalMatch
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow19AffineTop
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightAffineTops
import SymmetricSubgroupAsymptotics.FaithfulFiniteActionImage

/-! Actual published8/16 action charts exclude the remaining binary-degree
nonaffine numerical possibilities. The affine branches use their original
proved semidirect-product isomorphisms; the natural branches use their actual
normal quotients. No abstract order-only classification is inferred. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical Pointwise
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [Nontrivial X] [MulAction.IsPreprimitive G X]

omit [Nontrivial X] in
theorem NonaffineData.oneFactor_degreeSixteen_quotient_card_le_two
    (D : NonaffineData G X) (hk : D.factorCount=1)
    (published : PrimitiveSixteenCanonicalCatalogue.PublishedClassification)
    (hX : Nat.card X=16) : Nat.card (G⧸finiteGroupSocle G)≤2 := by
  let points : X≃Fin 16 := Finite.equivFinOfCardEq hX
  let S := labelledActionImage (A := G) points
  have hp : MulAction.IsPreprimitive S (Fin 16) :=
    (labelledAction_preprimitive_iff points).mp inferInstance
  obtain ⟨j,g,hg⟩ := PrimitiveSixteenCanonicalCatalogue.originalClassification published S hp
  let e : G≃*PrimitiveAffineSixteenAllLiteralFrames.top j :=
    (faithfulLabelledActionEquiv points).trans (actionConjugacyEquiv g hg)
  fin_cases j
  · exact (D.oneFactor_not_affineModel hk (by decide)
      PrimitiveAffineDegreeTwoPrimitiveSixteenRow1AffineSocles.linearGroup
      (e.trans PrimitiveAffineDegreeTwoPrimitiveSixteenRow1AffineSocles.modelEquiv)).elim
  · exact (D.oneFactor_not_affineModel hk (by decide)
      PrimitiveAffineDegreeTwoPrimitiveSixteenRow2AffineSocles.linearGroup
      (e.trans PrimitiveAffineDegreeTwoPrimitiveSixteenRow2AffineSocles.modelEquiv)).elim
  · exact (D.oneFactor_not_affineModel hk (by decide)
      PrimitiveAffineDegreeTwoPrimitiveSixteenRow3AffineSocles.linearGroup
      (e.trans PrimitiveAffineDegreeTwoPrimitiveSixteenRow3AffineSocles.modelEquiv)).elim
  · exact (D.oneFactor_not_affineModel hk (by decide)
      PrimitiveAffineDegreeTwoPrimitiveSixteenRow4AffineSocles.linearGroup
      (e.trans PrimitiveAffineDegreeTwoPrimitiveSixteenRow4AffineSocles.modelEquiv)).elim
  · exact (D.oneFactor_not_affineModel hk (by decide)
      PrimitiveAffineDegreeTwoPrimitiveSixteenRow5AffineSocles.linearGroup
      (e.trans PrimitiveAffineDegreeTwoPrimitiveSixteenRow5AffineSocles.modelEquiv)).elim
  · exact (D.oneFactor_not_affineModel hk (by decide)
      PrimitiveAffineDegreeTwoPrimitiveSixteenRow6AffineSocles.linearGroup
      (e.trans PrimitiveAffineDegreeTwoPrimitiveSixteenRow6AffineSocles.modelEquiv)).elim
  · exact (D.oneFactor_not_affineModel hk (by decide)
      PrimitiveAffineDegreeTwoPrimitiveSixteenRow7AffineSocles.linearGroup
      (e.trans PrimitiveAffineDegreeTwoPrimitiveSixteenRow7AffineSocles.modelEquiv)).elim
  · exact (D.oneFactor_not_affineModel hk (by decide)
      PrimitiveAffineDegreeTwoPrimitiveSixteenRow8AffineSocles.linearGroup
      (e.trans PrimitiveAffineDegreeTwoPrimitiveSixteenRow8AffineSocles.modelEquiv)).elim
  · exact (D.oneFactor_not_affineModel hk (by decide)
      PrimitiveAffineDegreeTwoPrimitiveSixteenRow9AffineSocles.linearGroup
      (e.trans PrimitiveAffineDegreeTwoPrimitiveSixteenRow9AffineSocles.modelEquiv)).elim
  · exact (D.oneFactor_not_affineModel hk (by decide)
      PrimitiveAffineDegreeTwoPrimitiveSixteenRow10AffineSocles.linearGroup
      (e.trans PrimitiveAffineDegreeTwoPrimitiveSixteenRow10AffineSocles.modelEquiv)).elim
  · exact (D.oneFactor_not_affineModel hk (by decide)
      PrimitiveAffineDegreeTwoPrimitiveSixteenRow11AffineSocles.linearGroup
      (e.trans PrimitiveAffineDegreeTwoPrimitiveSixteenRow11AffineSocles.modelEquiv)).elim
  · exact (D.oneFactor_not_affineModel hk (by decide)
      PrimitiveAffineDegreeTwoPrimitiveSixteenRow12AffineSocles.linearGroup
      (e.trans PrimitiveAffineDegreeTwoPrimitiveSixteenRow12AffineSocles.modelEquiv)).elim
  · exact (D.oneFactor_not_affineModel hk (by decide)
      PrimitiveAffineDegreeTwoPrimitiveSixteenRow13AffineSocles.linearGroup
      (e.trans PrimitiveAffineDegreeTwoPrimitiveSixteenRow13AffineSocles.modelEquiv)).elim
  · exact (D.oneFactor_not_affineModel hk (by decide)
      PrimitiveAffineDegreeTwoPrimitiveSixteenRow14AffineSocles.linearGroup
      (e.trans PrimitiveAffineDegreeTwoPrimitiveSixteenRow14AffineSocles.modelEquiv)).elim
  · exact (D.oneFactor_not_affineModel hk (by decide)
      PrimitiveAffineDegreeTwoPrimitiveSixteenRow15AffineSocles.linearGroup
      (e.trans PrimitiveAffineDegreeTwoPrimitiveSixteenRow15AffineSocles.modelEquiv)).elim
  · exact (D.oneFactor_not_affineModel hk (by decide)
      PrimitiveAffineDegreeTwoPrimitiveSixteenRow16AffineSocles.linearGroup
      (e.trans PrimitiveAffineDegreeTwoPrimitiveSixteenRow16AffineSocles.modelEquiv)).elim
  · exact (D.oneFactor_not_affineModel hk (by decide)
      PrimitiveAffineDegreeTwoPrimitiveSixteenRow17AffineSocles.linearGroup
      (e.trans PrimitiveAffineDegreeTwoPrimitiveSixteenRow17AffineSocles.modelEquiv)).elim
  · exact (D.oneFactor_not_affineModel hk (by decide)
      PrimitiveAffineDegreeTwoPrimitiveSixteenRow18AffineSocles.linearGroup
      (e.trans PrimitiveAffineDegreeTwoPrimitiveSixteenRow18AffineSocles.modelEquiv)).elim
  · exact (D.oneFactor_not_affineModel hk (by decide)
      PrimitiveAffineDegreeTwoPrimitiveSixteenRow19AffineSocles.linearGroup
      (e.trans PrimitiveAffineDegreeTwoPrimitiveSixteenRow19AffineSocles.modelEquiv)).elim
  · exact (D.oneFactor_not_affineModel hk (by decide)
      PrimitiveAffineDegreeTwoPrimitiveSixteenRow20AffineSocles.linearGroup
      (e.trans PrimitiveAffineDegreeTwoPrimitiveSixteenRow20AffineSocles.modelEquiv)).elim
  · exact quotient_card_le_two_of_alternating_equiv 16 (by decide)
      (show G≃*alternatingGroup (Fin 16) from e) (finiteGroupSocle G)
      (D.oneFactor_socle_nontrivial hk)
  · exact quotient_card_le_two_of_symmetric_equiv 16 (by decide)
      (e.trans Subgroup.topEquiv) (finiteGroupSocle G) (D.oneFactor_socle_nontrivial hk)

private theorem excludeEightLiteral
    (D : NonaffineData G X) (hk : D.factorCount=1)
    (j : Fin 24) (hj : 17≤j.val)
    (e : G≃*(DegreeTwoPairedEightSharedTops.interface j).top)
    (hcard : Nat.card G=1344) : False := by
  have hc := Nat.card_congr e.toEquiv
  rw [hcard] at hc
  fin_cases j
  · norm_num at hj
  · norm_num at hj
  · norm_num at hj
  · norm_num at hj
  · norm_num at hj
  · norm_num at hj
  · norm_num at hj
  · norm_num at hj
  · norm_num at hj
  · norm_num at hj
  · norm_num at hj
  · norm_num at hj
  · norm_num at hj
  · norm_num at hj
  · norm_num at hj
  · norm_num at hj
  · norm_num at hj
  · exact D.oneFactor_not_affineModel hk (by decide)
      PrimitiveAffineDegreeTwoPairedEightAffineTops.Row18.linearGroup
      (e.trans PrimitiveAffineDegreeTwoPairedEightAffineTops.Row18.modelEquiv)
  · exact D.oneFactor_not_affineModel hk (by decide)
      PrimitiveAffineDegreeTwoPairedEightRow19AffineTop.linearGroup
      (e.trans PrimitiveAffineDegreeTwoPairedEightRow19AffineTop.modelEquiv)
  · exact D.oneFactor_not_affineModel hk (by decide)
      PrimitiveAffineDegreeTwoPairedEightAffineTops.Row20.linearGroup
      (e.trans PrimitiveAffineDegreeTwoPairedEightAffineTops.Row20.modelEquiv)
  · letI : Group PrimitiveAffineEightFrameRow28TopCertificate.Source :=
      PrimitiveAffineEightFrameRow28TopCertificate.group
    have ht : Nat.card (DegreeTwoPairedEightSharedTops.interface (20 : Fin 24)).top=168 := by
      change Nat.card (Subgroup.closure (Set.range PrimitiveAffineEightFrameRow28TopCertificate.generators))=168
      rw [←Nat.card_congr PrimitiveAffineEightFrameRow28TopCertificate.originalEquiv.toEquiv]
      exact PrimitiveAffineEightFrameRow28TopCertificate.source_card
    change 1344=Nat.card (DegreeTwoPairedEightSharedTops.interface (20 : Fin 24)).top at hc
    rw [ht] at hc
    norm_num at hc
  · letI : Group PrimitiveAffineEightFrameRow29TopCertificate.Source :=
      PrimitiveAffineEightFrameRow29TopCertificate.group
    have ht : Nat.card (DegreeTwoPairedEightSharedTops.interface (21 : Fin 24)).top=336 := by
      change Nat.card (Subgroup.closure (Set.range PrimitiveAffineEightFrameRow29TopCertificate.generators))=336
      rw [←Nat.card_congr PrimitiveAffineEightFrameRow29TopCertificate.originalEquiv.toEquiv]
      exact PrimitiveAffineEightFrameRow29TopCertificate.source_card
    change 1344=Nat.card (DegreeTwoPairedEightSharedTops.interface (21 : Fin 24)).top at hc
    rw [ht] at hc
    norm_num at hc
  · change 1344=Nat.card DegreeTwoPairedEightSharedTops.Top23 at hc
    rw [DegreeTwoPairedEightSharedTops.top23_eq_alternating,nat_card_alternatingGroup,
      Nat.card_fin] at hc
    norm_num [Nat.factorial] at hc
  · change 1344=Nat.card DegreeTwoPairedEightSharedTops.Top24 at hc
    rw [DegreeTwoPairedEightSharedTops.top24_eq_top,Subgroup.card_top,Nat.card_perm,Nat.card_fin] at hc
    norm_num [Nat.factorial] at hc

theorem NonaffineData.oneFactor_degreeEight_card_ne_1344
    (D : NonaffineData G X) (hk : D.factorCount=1)
    (published : DegreeEightCanonicalCatalogue.PublishedClassification)
    (hX : Nat.card X=8) : Nat.card G≠1344 := by
  intro hcard
  let points : X≃Fin 8 := Finite.equivFinOfCardEq hX
  let S := labelledActionImage (A := G) points
  letI : MulAction.IsPreprimitive S (Fin 8) :=
    (labelledAction_preprimitive_iff points).mp inferInstance
  let M := DegreeEightCanonicalCatalogue.primitiveLiteralMatch published S (by simp)
  let e : G≃*(DegreeTwoPairedEightSharedTops.interface M.index).top :=
    (faithfulLabelledActionEquiv points).trans M.groupEquiv
  exact excludeEightLiteral D hk M.index M.primitive_index e hcard

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
