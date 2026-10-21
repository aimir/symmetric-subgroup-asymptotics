import SymmetricSubgroupAsymptotics.PrimitiveSmallBinaryNonaffineQuotient
import SymmetricSubgroupAsymptotics.PrimitiveOuterOrderRoundingGap
import SymmetricSubgroupAsymptotics.PrimitiveSmallSocleSingleFactor

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
    (hindex : PublishedSimpleIndexBounds) (hX : Nat.card X=8)
    (hG : Nat.card G=168 ∨ Nat.card G=336) :
    Nat.card (G⧸finiteGroupSocle G)≤7 := by
  obtain ⟨ell,_,hf,he,hlog⟩ := D.oneFactor_quotient_log_bound hk hindex
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
    (hindex : PublishedSimpleIndexBounds) (hX : Nat.card X=8)
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

theorem NonaffineData.degreeEight_quotient_card_le_seven
    (D : NonaffineData G X) (hindex : PublishedSimpleIndexBounds)
    (published : DegreeEightCanonicalCatalogue.PublishedClassification)
    (hX : Nat.card X=8) : Nat.card (G⧸finiteGroupSocle G)≤7 := by
  have hk := D.factorCount_one_of_degree_lt_twentyFive hindex (by omega)
  let points : X≃Fin 8 := Finite.equivFinOfCardEq hX
  let S := labelledActionImage (A := G) points
  letI : MulAction.IsPreprimitive S (Fin 8) :=
    (labelledAction_preprimitive_iff points).mp inferInstance
  let M := DegreeEightCanonicalCatalogue.primitiveLiteralMatch published S (by simp)
  let e : G≃*(DegreeTwoPairedEightSharedTops.interface M.index).top :=
    (faithfulLabelledActionEquiv points).trans M.groupEquiv
  exact from_literal D hk hindex hX M.index M.primitive_index e

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
