import SymmetricSubgroupAsymptotics.CFSGTrialityGeckGeneratedActionImage
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckRootGeneratedPGroup
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckDerivedProjectiveImage
import SymmetricSubgroupAsymptotics.CFSGGoodSylowOfTwoPSubgroups
import SymmetricSubgroupAsymptotics.CFSGGoodSylowPrimeSurjective

/-! Actual defining-prime good-Sylow witnesses for the ORIGINAL simple
triality D4 model. Genuine fixed root groups generate its derived action
image, while the same image already has a soluble Sylow normalizer.
The final passage is through the proved original projective equivalence. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckGoodSylow
open CFSGTrialityGeckGeneratedActionImage CFSGTrialityGeckDerivedRootGeneration
open CFSGTrialityGeckRelativeRootGenerated CFSGTrialityGeckRootGeneratedPGroup
open CFSGTrialityGeckSourceWordAction CFSGTrialityGeckLongDerivedImage
open CFSGTrialityGeckDerivedSylowNormalizer CFSGTrialityGeckDerivedProjectiveImage
open CFSGSerreOrdinaryTwists CFSGReduction

def generatedToDerived (q : CFSG.PrimePower) :
    fixedRootGenerated (q.Extension 3) (definingFieldAutomorphism q 3) →*
      (derivedImageAction q).range :=
  (generatedAction (q.Extension 3) (definingFieldAutomorphism q 3)).codRestrict _
    (fun x => generated_action_range_le_original_derived q ⟨x,rfl⟩)

theorem generatedToDerived_surjective (q : CFSG.PrimePower) :
    Function.Surjective (generatedToDerived q) := by
  intro y
  have hy : y.val ∈ (generatedAction (q.Extension 3) (definingFieldAutomorphism q 3)).range := by
    rw [generated_action_range_eq_original_derived]
    exact y.property
  obtain ⟨x,hx⟩ := hy
  exact ⟨x,Subtype.ext hx⟩

theorem derived_image_goodSylowPrime (q : CFSG.PrimePower) :
    GoodSylowPrime (derivedImageAction q).range q.prime := by
  let H := (derivedImageAction q).range
  letI : Finite H := Finite.of_surjective (preimageToImage q) (preimageToImage_surjective q)
  let U := (rootPart (q.Extension 3) (definingFieldAutomorphism q 3) false).map (generatedToDerived q)
  let V := (rootPart (q.Extension 3) (definingFieldAutomorphism q 3) true).map (generatedToDerived q)
  have hU : IsPGroup q.prime U :=
    (rootPart_isPGroup (q.Extension 3) (definingFieldAutomorphism q 3) q.prime false).map (generatedToDerived q)
  have hV : IsPGroup q.prime V :=
    (rootPart_isPGroup (q.Extension 3) (definingFieldAutomorphism q 3) q.prime true).map (generatedToDerived q)
  have hgen : U ⊔ V = ⊤ := by
    change (rootPart (q.Extension 3) (definingFieldAutomorphism q 3) false).map (generatedToDerived q) ⊔
      (rootPart (q.Extension 3) (definingFieldAutomorphism q 3) true).map (generatedToDerived q) = ⊤
    rw [←Subgroup.map_sup,rootPart_sup,Subgroup.map_top_of_surjective _ (generatedToDerived_surjective q)]
  exact goodSylowPrime_of_two_p_subgroups_and_exists_soluble_normalizer U V hU hV hgen
    (exists_image_sylow_soluble_normalizer q)

theorem original_goodSylowPrime (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] :
    GoodSylowPrime (CFSG.Models.TrialityD4 q) q.prime := by
  let H := (derivedImageAction q).range
  letI : Finite H := Finite.of_surjective (preimageToImage q) (preimageToImage_surjective q)
  let e := originalProjectiveImageEquiv q
  let f := e.symm.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center H))
  have hf : Function.Surjective f :=
    e.symm.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center H))
  exact goodSylowPrime_surjective f hf (derived_image_goodSylowPrime q)

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckGoodSylow
