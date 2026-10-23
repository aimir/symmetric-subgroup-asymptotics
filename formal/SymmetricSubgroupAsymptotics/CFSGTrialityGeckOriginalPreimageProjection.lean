import SymmetricSubgroupAsymptotics.CFSGTrialityGeckPreimageOppositeAlignment
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalRootFamily

/-! The SAME derived-image preimage surjects onto the ORIGINAL simple
triality model and is injective on its actual positive Sylow. This is
the precise cover needed for opposite-pair alignment descent. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalPreimageProjection
open CFSGTrialityGeckDerivedSylowNormalizer CFSGTrialityGeckFixedPositiveImageSylow
open CFSGTrialityGeckOriginalIndexSquare CFSGTrialityGeckOriginalRootFamily

private theorem injective_cover_comp {G H J : Type*} [Group G] [Group H] [Group J]
    (f : G→*H) (g : H→*J) (P : Subgroup G) (Q : Subgroup H)
    (hf : Function.Injective (f.comp P.subtype)) (hPQ : P.map f≤Q)
    (hg : Function.Injective (g.comp Q.subtype)) :
    Function.Injective ((g.comp f).comp P.subtype) := by
  intro x y he
  apply hf
  have hx : f x.val∈Q := hPQ ⟨x.val,x.property,rfl⟩
  have hy : f y.val∈Q := hPQ ⟨y.val,y.property,rfl⟩
  have hh : (⟨f x.val,hx⟩ : Q)=⟨f y.val,hy⟩ := hg he
  exact congrArg Subtype.val hh

def originalPreimageProjection (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] :
    naturalDerivedPreimage q→*CFSG.Models.TrialityD4 q :=
  (originalProjection q).comp (preimageToImage q)

theorem originalPreimageProjection_surjective (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] : Function.Surjective (originalPreimageProjection q) :=
  (originalProjection_surjective q).comp (preimageToImage_surjective q)

theorem originalPreimageProjection_positive_injective (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] :
    Function.Injective ((originalPreimageProjection q).comp
      (preimageSylow q : Subgroup (naturalDerivedPreimage q)).subtype) := by
  apply injective_cover_comp (preimageToImage q) (originalProjection q)
    (preimageSylow q : Subgroup (naturalDerivedPreimage q))
    (imagePositiveSylow q : Subgroup (DerivedImage q)) (preimage_sylow_action_injective q)
    ?_ (originalProjection_sylow_injective q)
  exact le_of_eq (show (preimageSylow q : Subgroup (naturalDerivedPreimage q)).map (preimageToImage q)=
    (imagePositiveSylow q : Subgroup (DerivedImage q)) from rfl)

theorem originalPreimageProjection_positive_image (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] :
    (preimageSylow q : Subgroup (naturalDerivedPreimage q)).map (originalPreimageProjection q)=
      (originalSylow q : Subgroup (CFSG.Models.TrialityD4 q)) := by
  change (preimageSylow q : Subgroup (naturalDerivedPreimage q)).map
    ((originalProjection q).comp (preimageToImage q))=_
  rw [←Subgroup.map_map]
  rfl

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalPreimageProjection
