import SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeSignedGroups
import SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeDerivedImage
import SymmetricSubgroupAsymptotics.CFSGTwistedDDerivedSylowNormalizer
import SymmetricSubgroupAsymptotics.CFSGTwoPSubgroupsSylowGeneration
import SymmetricSubgroupAsymptotics.CFSGSolubleSylowNormalizerConjugacy
import SymmetricSubgroupAsymptotics.CFSGGoodSylowPrimeSurjective

/-! Two genuine signed relative p-subgroups generate the whole original
Derived action image. Its proved soluble Sylow normalizer then supplies
GoodSylowPrime, and the SAME original simple model receives the witness. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeGoodSylow
open CFSGTwistedDRelativeElementaryGroup CFSGTwistedDRelativeSignedGroups
open CFSGTwistedDRelativeDerivedImage

theorem relative_image_goodSylowPrime (s : ℕ) (q : CFSG.PrimePower) :
    CFSGReduction.GoodSylowPrime (relativeImageAction s q).range q.prime := by
  letI : Finite (relativeImageAction s q).range :=
    Finite.of_surjective (relativeImageAction s q).rangeRestrict
      (relativeImageAction s q).rangeRestrict_surjective
  let R := relativeRootGroup (s + 2) q
  let U := signedRootGroup (s + 2) q false
  let V := signedRootGroup (s + 2) q true
  have hjoin : U ⊔ V = R := positive_sup_negative (s + 2) q
  have hU : U ≤ R := by rw [← hjoin]; exact le_sup_left
  have hV : V ≤ R := by rw [← hjoin]; exact le_sup_right
  have hUp : IsPGroup q.prime (U.subgroupOf R) :=
    (signedRootGroup_isPGroup (s + 2) q false).of_injective
      (Subgroup.subgroupOfEquivOfLe hU).toMonoidHom (Subgroup.subgroupOfEquivOfLe hU).injective
  have hVp : IsPGroup q.prime (V.subgroupOf R) :=
    (signedRootGroup_isPGroup (s + 2) q true).of_injective
      (Subgroup.subgroupOfEquivOfLe hV).toMonoidHom (Subgroup.subgroupOfEquivOfLe hV).injective
  have htop : U.subgroupOf R ⊔ V.subgroupOf R = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hU hV, hjoin, Subgroup.subgroupOf_self]
  let f := (relativeImageAction s q).rangeRestrict
  have himage : (U.subgroupOf R).map f ⊔ (V.subgroupOf R).map f = ⊤ := by
    rw [← Subgroup.map_sup, htop, Subgroup.map_top_of_surjective f
      (relativeImageAction s q).rangeRestrict_surjective]
  obtain ⟨P, g, _, hg⟩ := CFSGTwoPSubgroupsSylowGeneration.exists_conjugate_sylows
    ((U.subgroupOf R).map f) ((V.subgroupOf R).map f) (hUp.map f) (hVp.map f) himage
  let e := MulEquiv.subgroupCongr (action_ranges_eq s q)
  letI : Finite (CFSGTwistedDDerivedPairedRoots.derivedImageAction s q).range :=
    Finite.of_injective e e.injective
  have hnormal := CFSGSolubleSylowNormalizerSurjective.exists_sylow_soluble_normalizer_map
    e.toMonoidHom e.surjective
    (CFSGTwistedDDerivedSylowNormalizer.exists_image_sylow_soluble_normalizer s q)
  exact ⟨q.prime_isPrime, P, g, CFSGSolubleSylowNormalizerConjugacy.all_of_exists hnormal P, hg⟩

theorem original_goodSylowPrime (s : ℕ) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedD (s + 4) q)] :
    CFSGReduction.GoodSylowPrime (CFSG.Models.TwistedD (s + 4) q) q.prime := by
  let H := (relativeImageAction s q).range
  letI : Finite H := Finite.of_surjective (relativeImageAction s q).rangeRestrict
    (relativeImageAction s q).rangeRestrict_surjective
  let Q := QuotientGroup.mk' (Subgroup.center H)
  let e := originalProjectiveRelativeImageEquiv s q
  let f := e.symm.toMonoidHom.comp Q
  have hf : Function.Surjective f :=
    e.symm.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center H))
  exact CFSGReduction.goodSylowPrime_surjective f hf (relative_image_goodSylowPrime s q)

end SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeGoodSylow
