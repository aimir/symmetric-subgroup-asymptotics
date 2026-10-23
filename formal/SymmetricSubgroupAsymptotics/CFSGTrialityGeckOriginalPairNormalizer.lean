import SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalSimpleParameters
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedPairNormalizer
import SymmetricSubgroupAsymptotics.CFSGCentralKernelPSubgroupReflection

/-! The intrinsic simultaneous normalizer in the SAME original model
pulls back exactly to the genuine fixed-pair normalizer in J. The
reflection uses central p-element separation, not mere separate
injectivity on the two opposed subgroups. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalPairNormalizer
open CFSGTrialityGeckOriginalSimpleParameters CFSGTrialityGeckFixedPairNormalizer
open CFSGTrialityGeckGeneratedOriginalProjection CFSGTrialityGeckGeneratedOriginalCentralKernel
open CFSGTrialityGeckGeneratedPositiveSylow CFSGTrialityGeckGeneratedPreimageCoordinates
open CFSGTrialityGeckRelativeRootGenerated CFSGTrialityGeckRootGeneratedPGroup
open CFSGTrialityGeckOriginalOppositeSylows CFSGSerreOrdinaryTwists
open CFSGTrialityGeckOriginalRootFamily CFSGTrialityGeckOriginalOppositeAlignment
local instance (q : CFSG.PrimePower) : Fact q.prime.Prime := ⟨q.prime_isPrime⟩

private theorem injective_subtype_of_eq {G H : Type*} [Group G] [Group H]
    (f : G→*H) (P Q : Subgroup G) (he : P=Q)
    (hinj : Function.Injective (f.comp Q.subtype)) : Function.Injective (f.comp P.subtype) := by
  subst P
  exact hinj

def originalPairNormalizer (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.TrialityD4 q)] : Subgroup (CFSG.Models.TrialityD4 q) :=
  Subgroup.normalizer (originalSylow q : Set (CFSG.Models.TrialityD4 q))⊓
    Subgroup.normalizer (originalNegative q : Set (CFSG.Models.TrialityD4 q))

theorem mem_originalPairNormalizer_iff (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)]
    (g : fixedRootGenerated (q.Extension 3) (definingFieldAutomorphism q 3)) :
    generatedToOriginal q g∈originalPairNormalizer q↔
      g.val∈pairNormalizer (q.Extension 3) (definingFieldAutomorphism q 3) := by
  have hpinj : Function.Injective ((generatedToOriginal q).comp
      (generatedPositiveSylow q : Subgroup
        (fixedRootGenerated (q.Extension 3) (definingFieldAutomorphism q 3))).subtype) :=
    injective_subtype_of_eq (generatedToOriginal q) _ _
      (generatedPositiveSylow_coe q) (rootPart_positive_original_injective q)
  have hsign (neg:Bool) :
      generatedToOriginal q g∈Subgroup.normalizer
        ((rootPart (q.Extension 3) (definingFieldAutomorphism q 3) neg).map
          (generatedToOriginal q) : Set (CFSG.Models.TrialityD4 q))↔
      g.val∈Subgroup.normalizer (signedFixed (q.Extension 3)
        (definingFieldAutomorphism q 3) neg : Set _) := by
    rw [CFSGCentralKernelPSubgroupReflection.mem_normalizer_map_iff (generatedToOriginal q)
      (generatedPositiveSylow q) hpinj (generatedToOriginal_kernel_le_center q) _
      (rootPart_isPGroup _ _ q.prime neg)]
    change g∈Subgroup.normalizer ((signedFixed (q.Extension 3)
        (definingFieldAutomorphism q 3) neg).subgroupOf
          (fixedRootGenerated (q.Extension 3) (definingFieldAutomorphism q 3)) : Set _)↔_
    rw [←Subgroup.subgroupOf_normalizer_eq (signedFixed_le_generated _ _ neg)]
    rfl
  have hp := hsign false
  have hn := hsign true
  rw [rootPart_positive_original_image] at hp
  rw [rootPart_negative_original_image] at hn
  constructor
  · intro hg
    exact ⟨⟨hp.mp hg.1,hn.mp hg.2⟩,g.property⟩
  · intro hg
    exact ⟨hp.mpr hg.1.1,hn.mpr hg.1.2⟩

theorem originalPairNormalizer_map (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] (f : MulAut (CFSG.Models.TrialityD4 q))
    (hp : (originalSylow q).map f.toMonoidHom=originalSylow q)
    (hn : (originalNegative q).map f.toMonoidHom=originalNegative q) :
    (originalPairNormalizer q).map f.toMonoidHom=originalPairNormalizer q := by
  have hP : (Subgroup.normalizer (originalSylow q : Set (CFSG.Models.TrialityD4 q))).map
      f.toMonoidHom=Subgroup.normalizer (originalSylow q : Set (CFSG.Models.TrialityD4 q)) :=
    (Subgroup.map_equiv_normalizer_eq (originalSylow q : Subgroup (CFSG.Models.TrialityD4 q)) f).trans
      (congrArg (fun S:Subgroup (CFSG.Models.TrialityD4 q)=>Subgroup.normalizer
        (S:Set (CFSG.Models.TrialityD4 q))) hp)
  have hN : (Subgroup.normalizer (originalNegative q : Set (CFSG.Models.TrialityD4 q))).map
      f.toMonoidHom=Subgroup.normalizer (originalNegative q : Set (CFSG.Models.TrialityD4 q)) :=
    (Subgroup.map_equiv_normalizer_eq (originalNegative q) f).trans
      (congrArg (fun S:Subgroup (CFSG.Models.TrialityD4 q)=>Subgroup.normalizer
        (S:Set (CFSG.Models.TrialityD4 q))) hn)
  rw [originalPairNormalizer,Subgroup.map_inf _ _ _ f.injective,hP,hN]

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalPairNormalizer
