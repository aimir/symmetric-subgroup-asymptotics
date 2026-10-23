import SymmetricSubgroupAsymptotics.CFSGE6GeckDiagonalSimpleScalars
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalUpperNormalizer
import SymmetricSubgroupAsymptotics.CFSGCentralKernelPSubgroupReflection

/-! Six literal ambient scalar actions for the ORIGINAL twisted E6
opposed-pair normalizer. The SAME central quotient reflects the actual
positive and negative p-subgroups. Only elements are lifted to J. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalPairNormalizer
open CFSGE6GeckDiagonalSimpleScalars CFSGE6GeckFixedPairNormalizer
open CFSGTwistedE6GeckOriginalProjection CFSGTwistedE6GeckOriginalOppositeAlignment
open CFSGTwistedE6GeckOriginalCentralKernel CFSGTwistedE6GeckGeneratedPositiveSylow
open CFSGTwistedE6GeckRelativeRootGenerated CFSGTwistedE6GeckRootGeneratedPGroup
open CFSGTwistedE6GeckDiagramCovariance CFSGSerreOrdinaryTwists
open CFSGCentralKernelPSubgroupReflection CFSGSerreQuadraticMatrix
local instance (q:CFSG.PrimePower) : Fact q.prime.Prime := ⟨q.prime_isPrime⟩

private theorem injective_subtype_of_eq {G H:Type*} [Group G] [Group H]
    (f:G→*H) (P Q:Subgroup G) (he:P=Q) (hi:Function.Injective (f.comp Q.subtype)) :
    Function.Injective (f.comp P.subtype) := by
  subst P
  exact hi

def originalPairNormalizer (q:CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.TwistedE6 q)] :
    Subgroup (CFSG.Models.TwistedE6 q) :=
  Subgroup.normalizer (originalPositiveSylow q : Set (CFSG.Models.TwistedE6 q))⊓
    Subgroup.normalizer (originalNegative q : Set (CFSG.Models.TwistedE6 q))

theorem mem_originalPairNormalizer_iff (q:CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)]
    (g:fixedRootGenerated (q.Extension 2) (definingFieldAutomorphism q 2)) :
    generatedToOriginal q g∈originalPairNormalizer q↔
      g.val∈pairNormalizer (q.Extension 2) (definingFieldAutomorphism q 2) := by
  have hpinj : Function.Injective ((generatedToOriginal q).comp
      (generatedPositiveSylow q : Subgroup (fixedRootGenerated (q.Extension 2)
        (definingFieldAutomorphism q 2))).subtype) :=
    injective_subtype_of_eq (generatedToOriginal q) _ _ (generatedPositiveSylow_coe q)
      (rootPart_positive_original_injective q)
  have hsign (neg:Bool) :
      generatedToOriginal q g∈Subgroup.normalizer
        ((rootPart (q.Extension 2) (definingFieldAutomorphism q 2) neg).map (generatedToOriginal q) :
          Set (CFSG.Models.TwistedE6 q))↔
      g.val∈Subgroup.normalizer
        (signedFixed (q.Extension 2) (definingFieldAutomorphism q 2) neg :
          Set (Matrix GeckIndex GeckIndex (q.Extension 2))ˣ) := by
    rw [mem_normalizer_map_iff (generatedToOriginal q) (generatedPositiveSylow q)
      hpinj (generatedToOriginal_kernel_le_center q) _ (rootPart_isPGroup _ _ q.prime neg)]
    change g∈Subgroup.normalizer ((signedFixed (q.Extension 2) (definingFieldAutomorphism q 2) neg).subgroupOf
      (fixedRootGenerated (q.Extension 2) (definingFieldAutomorphism q 2)) : Set _)↔_
    rw [←Subgroup.subgroupOf_normalizer_eq (signedFixed_le_generated _ _ neg)]
    rfl
  have hp := hsign false
  have hn := hsign true
  rw [rootPart_positive_original_image] at hp
  change generatedToOriginal q g∈Subgroup.normalizer
    (originalNegative q : Set (CFSG.Models.TwistedE6 q))↔_ at hn
  exact ⟨fun h=>⟨⟨hp.mp h.1,hn.mp h.2⟩,g.property⟩,
    fun h=>⟨hp.mpr h.1.1,hn.mpr h.1.2⟩⟩

theorem originalPairNormalizer_raw_positive_scalars (q:CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)]
    (d:CFSG.Models.TwistedE6 q) (hd:d∈originalPairNormalizer q) :
    ∃g:fixedRootGenerated (q.Extension 2) (definingFieldAutomorphism q 2),
      generatedToOriginal q g=d ∧ ∃c:Fin 6→(q.Extension 2)ˣ,∀i t,
        g.val*canonicalRoot rawData (q.Extension 2) false i t*g.val⁻¹=
          canonicalRoot rawData (q.Extension 2) false i ((c i:q.Extension 2)*t) := by
  obtain ⟨g,rfl⟩ := generatedToOriginal_surjective q d
  have hg := (mem_originalPairNormalizer_iff q g).mp hd
  choose c hc using fun i:Fin 6=>
    pairNormalizer_simple_scalar (q.Extension 2) (definingFieldAutomorphism q 2) g.val hg i
  exact ⟨g,rfl,c,hc⟩

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalPairNormalizer
