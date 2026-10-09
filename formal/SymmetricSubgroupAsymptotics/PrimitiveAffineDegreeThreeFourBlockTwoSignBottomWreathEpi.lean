import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockTwoSignBottomLinearImage
import Mathlib.GroupTheory.SchurZassenhaus

/-!
# The rank-two bottom maps onto the ternary wreath comparator

Schur--Zassenhaus splits the original group over its rank-two ternary
translation layer.  The action-compatible bottom `D8` recognition maps the
chosen binary complement onto the standard dihedral top.  Together with the
literal translation coordinates this gives an epimorphism from the original
group onto `S₃ ≀ C₂`.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

private abbrev G := preE7NonPairAction w U

local instance : Fact P.p.Prime := (chart block P).primeFact

/-- The original four-block group splits over its literal ternary
translation intersection when the signed quotient is binary. -/
theorem degreeThreeFourBlockTwoSignBottomComplement_exists
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action) :
    ∃ H : Subgroup G,
      Subgroup.IsComplement' (E block P) H := by
  have hkernel : IsPGroup 3 (E block P) :=
    degreeThreeFourBlock_translationIntersection_isPGroup block P hr
  have htop : IsPGroup 2 (G ⧸ E block P) :=
    degreeThreeFourBlock_signedQuotient_isPGroup
      block P hr hs hcomponent hbinary
  obtain ⟨a, ha⟩ := hkernel.exists_card_eq
  obtain ⟨c, hc⟩ := htop.exists_card_eq
  apply Subgroup.exists_right_complement'_of_coprime
  have hindex : (E block P).index = Nat.card (G ⧸ E block P) := by
    rw [QuotientGroup.card_quotient]
  rw [ha, hindex, hc]
  exact (Nat.Coprime.pow_left a
    (by decide : Nat.Coprime 3 2)).pow_right c

/-- A fixed literal Schur complement to the rank-two translation layer. -/
noncomputable def degreeThreeFourBlockTwoSignBottomComplement
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action) :
    Subgroup G :=
  Classical.choose
    (degreeThreeFourBlockTwoSignBottomComplement_exists
      block P hr hs hcomponent hbinary)

theorem degreeThreeFourBlockTwoSignBottomComplement_isComplement
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action) :
    Subgroup.IsComplement' (E block P)
      (degreeThreeFourBlockTwoSignBottomComplement
        block P hr hs hcomponent hbinary) :=
  Classical.choose_spec
    (degreeThreeFourBlockTwoSignBottomComplement_exists
      block P hr hs hcomponent hbinary)

/-- Restriction of the signed quotient map to a chosen bottom complement. -/
def degreeThreeFourBlockTwoSignBottomComplementTopHom
    (H : Subgroup G) : H →* G ⧸ E block P :=
  (QuotientGroup.mk' (E block P)).comp H.subtype

/-- A complementary subgroup embeds into the signed quotient. -/
theorem degreeThreeFourBlockTwoSignBottomComplementTopHom_injective
    (H : Subgroup G)
    (hH : Subgroup.IsComplement' (E block P) H) :
    Function.Injective
      (degreeThreeFourBlockTwoSignBottomComplementTopHom block P H) := by
  intro x y hxy
  have hker : (x : G)⁻¹ * (y : G) ∈ E block P := by
    rw [← QuotientGroup.ker_mk' (E block P)]
    apply MonoidHom.mem_ker.mpr
    change (QuotientGroup.mk' (E block P) (x : G))⁻¹ *
      QuotientGroup.mk' (E block P) (y : G) = 1
    rw [hxy, inv_mul_cancel]
  have hmemH : (x : G)⁻¹ * (y : G) ∈ H :=
    H.mul_mem (H.inv_mem x.property) y.property
  have hbot : (x : G)⁻¹ * (y : G) ∈ (⊥ : Subgroup G) :=
    hH.disjoint.le_bot ⟨hker, hmemH⟩
  apply Subtype.ext
  exact inv_mul_eq_one.mp (Subgroup.mem_bot.mp hbot)

/-- A bottom complement is exactly the signed quotient. -/
noncomputable def degreeThreeFourBlockTwoSignBottomComplementTopEquiv
    (H : Subgroup G)
    (hH : Subgroup.IsComplement' (E block P) H) :
    H ≃* G ⧸ E block P := by
  let f := degreeThreeFourBlockTwoSignBottomComplementTopHom block P H
  apply MulEquiv.ofBijective f
  apply (Nat.bijective_iff_injective_and_card f).mpr
  refine ⟨degreeThreeFourBlockTwoSignBottomComplementTopHom_injective
    block P H hH, ?_⟩
  calc
    Nat.card H = (E block P).index := hH.card_right
    _ = Nat.card (G ⧸ E block P) := by
      rw [QuotientGroup.card_quotient]

@[simp] theorem degreeThreeFourBlockTwoSignBottomComplementTopEquiv_apply
    (H : Subgroup G)
    (hH : Subgroup.IsComplement' (E block P) H)
    (h : H) :
    degreeThreeFourBlockTwoSignBottomComplementTopEquiv
        block P H hH h = QuotientGroup.mk' (E block P) h := rfl

/-- Internal semidirect coordinates on the original bottom extension. -/
noncomputable def degreeThreeFourBlockTwoSignBottomSemidirectEquiv
    (H : Subgroup G)
    (hH : Subgroup.IsComplement' (E block P) H) :
    E block P ⋊[((E block P).normalizerMonoidHom).comp
        (Subgroup.inclusion ((E block P).normalizer_eq_top ▸ le_top))] H ≃*
      G :=
  SemidirectProduct.mulEquivSubgroup hH

/-- The chosen bottom complement maps onto the standard dihedral top. -/
noncomputable def degreeThreeFourBlockTwoSignBottomComplementD8Map
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (hfin : Module.finrank (ZMod P.p)
      (TranslationSubmodule block P) = 2) :
    degreeThreeFourBlockTwoSignBottomComplement
        block P hr hs hcomponent hbinary →* DegreeSixS3Wreath.D8 :=
  (degreeThreeFourBlockTwoSignBottomD8Map
      block P hr hs hcomponent hbinary htwo hfin).comp
    (degreeThreeFourBlockTwoSignBottomComplementTopEquiv
      block P
      (degreeThreeFourBlockTwoSignBottomComplement
        block P hr hs hcomponent hbinary)
      (degreeThreeFourBlockTwoSignBottomComplement_isComplement
        block P hr hs hcomponent hbinary)).toMonoidHom

theorem degreeThreeFourBlockTwoSignBottomComplementD8Map_surjective
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (hfin : Module.finrank (ZMod P.p)
      (TranslationSubmodule block P) = 2) :
    Function.Surjective
      (degreeThreeFourBlockTwoSignBottomComplementD8Map
        block P hr hs hcomponent hbinary htwo hfin) :=
  (degreeThreeFourBlockTwoSignBottomD8Map_surjective
      block P hr hs hcomponent hbinary htwo hfin).comp
    (degreeThreeFourBlockTwoSignBottomComplementTopEquiv
      block P
      (degreeThreeFourBlockTwoSignBottomComplement
        block P hr hs hcomponent hbinary)
      (degreeThreeFourBlockTwoSignBottomComplement_isComplement
        block P hr hs hcomponent hbinary)).surjective

/-- The literal translation kernel in standard ternary-plane coordinates. -/
noncomputable def degreeThreeFourBlockTwoSignBottomKernelTernaryEquiv
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (hfin : Module.finrank (ZMod P.p)
      (TranslationSubmodule block P) = 2) :
    E block P ≃* DegreeSixS3Wreath.TernaryKernel :=
  (translationMulEquiv block P).trans
    (degreeThreeFourBlockTwoSignBottomTernaryEquiv
      block P hr hs hcomponent hbinary htwo hfin).toMultiplicative

/-- The translation and complement maps respect the actual conjugation
action in the original group. -/
theorem degreeThreeFourBlockTwoSignBottomSemidirect_compatible
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (hfin : Module.finrank (ZMod P.p)
      (TranslationSubmodule block P) = 2) :
    let H := degreeThreeFourBlockTwoSignBottomComplement
      block P hr hs hcomponent hbinary
    ∀ h : H,
      (degreeThreeFourBlockTwoSignBottomKernelTernaryEquiv
          block P hr hs hcomponent hbinary htwo hfin).toMonoidHom.comp
          ((((E block P).normalizerMonoidHom).comp
            (Subgroup.inclusion
              ((E block P).normalizer_eq_top ▸ le_top))) h).toMonoidHom =
        (DegreeSixS3Wreath.monomialAction
          (degreeThreeFourBlockTwoSignBottomComplementD8Map
            block P hr hs hcomponent hbinary htwo hfin h)).toMonoidHom.comp
          (degreeThreeFourBlockTwoSignBottomKernelTernaryEquiv
            block P hr hs hcomponent hbinary htwo hfin).toMonoidHom := by
  let H := degreeThreeFourBlockTwoSignBottomComplement
    block P hr hs hcomponent hbinary
  let c := degreeThreeFourBlockTwoSignBottomTernaryEquiv
    block P hr hs hcomponent hbinary htwo hfin
  let topEquiv := degreeThreeFourBlockTwoSignBottomComplementTopEquiv
    block P H
      (degreeThreeFourBlockTwoSignBottomComplement_isComplement
        block P hr hs hcomponent hbinary)
  intro h
  apply MonoidHom.ext
  intro k
  apply Multiplicative.toAdd.injective
  let action := (((E block P).normalizerMonoidHom).comp
    (Subgroup.inclusion
      ((E block P).normalizer_eq_top ▸ le_top))) h
  have hkernel :
      (translationMulEquiv block P (action k)).toAdd =
        (elementaryChart block P).quotientRepresentation.ρ
          (topEquiv h) (translationMulEquiv block P k).toAdd := by
    rw [degreeThreeFourBlockTwoSignBottomComplementTopEquiv_apply]
    rw [(elementaryChart block P).quotientRepresentation_apply]
    rfl
  have haction := degreeThreeFourBlockTwoSignBottomTernaryEquiv_action
    block P hr hs hcomponent hbinary htwo hfin (topEquiv h)
      (translationMulEquiv block P k).toAdd
  change c ((translationMulEquiv block P (action k)).toAdd) = _
  rw [hkernel, DegreeSixS3Wreath.monomialAction_toAdd]
  simpa only [degreeThreeFourBlockTwoSignBottomKernelTernaryEquiv,
    degreeThreeFourBlockTwoSignBottomComplementD8Map,
    MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    degreeThreeFourBlockTwoSignBottomComplementTopEquiv_apply,
    topEquiv, c, H, action] using haction

/-- Semidirect-product epimorphism from the split bottom extension to the
canonical split model of `S₃ ≀ C₂`. -/
noncomputable def degreeThreeFourBlockTwoSignBottomSemidirectMap
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (hfin : Module.finrank (ZMod P.p)
      (TranslationSubmodule block P) = 2) :
    let H := degreeThreeFourBlockTwoSignBottomComplement
      block P hr hs hcomponent hbinary
    E block P ⋊[((E block P).normalizerMonoidHom).comp
        (Subgroup.inclusion ((E block P).normalizer_eq_top ▸ le_top))] H →*
      DegreeSixS3Wreath.SemidirectModel :=
  SemidirectProduct.map
    (degreeThreeFourBlockTwoSignBottomKernelTernaryEquiv
      block P hr hs hcomponent hbinary htwo hfin).toMonoidHom
    (degreeThreeFourBlockTwoSignBottomComplementD8Map
      block P hr hs hcomponent hbinary htwo hfin)
    (degreeThreeFourBlockTwoSignBottomSemidirect_compatible
      block P hr hs hcomponent hbinary htwo hfin)

theorem degreeThreeFourBlockTwoSignBottomSemidirectMap_surjective
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (hfin : Module.finrank (ZMod P.p)
      (TranslationSubmodule block P) = 2) :
    Function.Surjective
      (degreeThreeFourBlockTwoSignBottomSemidirectMap
        block P hr hs hcomponent hbinary htwo hfin) := by
  rintro ⟨v, d⟩
  obtain ⟨k, rfl⟩ :=
    (degreeThreeFourBlockTwoSignBottomKernelTernaryEquiv
      block P hr hs hcomponent hbinary htwo hfin).surjective v
  obtain ⟨h, rfl⟩ :=
    degreeThreeFourBlockTwoSignBottomComplementD8Map_surjective
      block P hr hs hcomponent hbinary htwo hfin d
  exact ⟨⟨k, h⟩, rfl⟩

/-- The original rank-two bottom maps onto the literal degree-six wreath
comparator. -/
noncomputable def degreeThreeFourBlockTwoSignBottomWreathMap
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (hfin : Module.finrank (ZMod P.p)
      (TranslationSubmodule block P) = 2) :
    G →* DegreeSixS3Wreath.G :=
  DegreeSixS3Wreath.semidirectEquiv.symm.toMonoidHom.comp
    ((degreeThreeFourBlockTwoSignBottomSemidirectMap
      block P hr hs hcomponent hbinary htwo hfin).comp
        (degreeThreeFourBlockTwoSignBottomSemidirectEquiv
          block P
          (degreeThreeFourBlockTwoSignBottomComplement
            block P hr hs hcomponent hbinary)
          (degreeThreeFourBlockTwoSignBottomComplement_isComplement
            block P hr hs hcomponent hbinary)).symm.toMonoidHom)

theorem degreeThreeFourBlockTwoSignBottomWreathMap_surjective
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (hfin : Module.finrank (ZMod P.p)
      (TranslationSubmodule block P) = 2) :
    Function.Surjective
      (degreeThreeFourBlockTwoSignBottomWreathMap
        block P hr hs hcomponent hbinary htwo hfin) :=
  DegreeSixS3Wreath.semidirectEquiv.symm.surjective.comp
    ((degreeThreeFourBlockTwoSignBottomSemidirectMap_surjective
      block P hr hs hcomponent hbinary htwo hfin).comp
        (degreeThreeFourBlockTwoSignBottomSemidirectEquiv
          block P
          (degreeThreeFourBlockTwoSignBottomComplement
            block P hr hs hcomponent hbinary)
          (degreeThreeFourBlockTwoSignBottomComplement_isComplement
            block P hr hs hcomponent hbinary)).symm.surjective)

/-- A rank-two ternary translation intersection has order nine. -/
theorem degreeThreeFourBlock_translationIntersection_card_of_finrank_two
    (hr : Nat.card block.Fibre = 3)
    (hfin : Module.finrank (ZMod P.p)
      (TranslationSubmodule block P) = 2) :
    Nat.card (E block P) = 9 := by
  have hp : P.p = 3 := (degreeThree_translation_prime_dim block P hr).1
  calc
    Nat.card (E block P) =
        Nat.card (Multiplicative (TranslationSubmodule block P)) :=
      Nat.card_congr (translationMulEquiv block P).toEquiv
    _ = Nat.card (TranslationSubmodule block P) := rfl
    _ = Nat.card (ZMod P.p) ^
        Module.finrank (ZMod P.p) (TranslationSubmodule block P) :=
      Module.natCard_eq_pow_finrank (K := ZMod P.p)
        (V := TranslationSubmodule block P)
    _ = 3 ^ 2 := by rw [Nat.card_zmod, hp, hfin]
    _ = 9 := by norm_num

/-- In the rank-two branch the original group has order at most 288. -/
theorem degreeThreeFourBlock_twoSign_rankTwo_order_le_two_eighty_eight
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (hfin : Module.finrank (ZMod P.p)
      (TranslationSubmodule block P) = 2) :
    Nat.card G ≤ 288 := by
  have hE := degreeThreeFourBlock_translationIntersection_card_of_finrank_two
    block P hr hfin
  have hquot := degreeThreeFourBlockTwoSign_signedQuotient_card_cases
    block P hr hs hcomponent hbinary htwo
  have hfactor :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (E block P)
  rw [hE] at hfactor
  rcases hquot with hquot | hquot <;> rw [hquot] at hfactor <;> omega

/-- The binary kernel left above the bottom wreath quotient has order at
most four. -/
theorem degreeThreeFourBlockTwoSignBottomWreathMap_kernel_card_le_four
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (hfin : Module.finrank (ZMod P.p)
      (TranslationSubmodule block P) = 2) :
    Nat.card (degreeThreeFourBlockTwoSignBottomWreathMap
      block P hr hs hcomponent hbinary htwo hfin).ker ≤ 4 := by
  let pi := degreeThreeFourBlockTwoSignBottomWreathMap
    block P hr hs hcomponent hbinary htwo hfin
  have hG : Nat.card G ≤ 288 :=
    degreeThreeFourBlock_twoSign_rankTwo_order_le_two_eighty_eight
      block P hr hs hcomponent hbinary htwo hfin
  have hfactor := pi.ker.card_mul_index
  have hindex : pi.ker.index = 72 := by
    rw [Subgroup.index_ker,
      pi.range_eq_top_of_surjective
        (degreeThreeFourBlockTwoSignBottomWreathMap_surjective
          block P hr hs hcomponent hbinary htwo hfin),
      Nat.card_congr Subgroup.topEquiv.toEquiv,
      DegreeSixS3Wreath.card_G]
  rw [hindex] at hfactor
  omega

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
