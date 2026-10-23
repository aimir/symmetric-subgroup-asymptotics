import SymmetricSubgroupAsymptotics.CFSGFFourE6PairNormalizerScalars
import SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalRootIntersection
import SymmetricSubgroupAsymptotics.CFSGCentralKernelPSubgroupReflection

/-! Scalar actions of the actual ORIGINAL F4 opposed-pair normalizer.
Reflection across the SAME central quotient retains the literal J and
its actual positive Sylow. No original automorphism is lifted. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalPairScalarAction
open CFSGFFourE6PairNormalizerScalars CFSGE6GeckFixedPairNormalizer
open CFSGFFourE6GeneratedOriginalProjection CFSGFFourE6OriginalProjection
open CFSGFFourE6OriginalRootIntersection CFSGFFourE6OriginalOppositeAlignment
open CFSGFFourE6PositiveSylow CFSGFFourSerreMatrices CFSGSerreQuadraticMatrix
open CFSGTwistedE6GeckRelativeRootGenerated CFSGTwistedE6GeckRootGeneratedPGroup
open CFSGTwistedE6GeckDiagramCovariance CFSGTwistedE6GeckMatrixTwist
open CFSGFFourE6SimpleGeneratedParameters CFSGFFourE6OriginalSimpleParameters
open CFSGCentralKernelPSubgroupReflection CFSG.Models.Chevalley

private def positiveInGenerated (K:Type) [Field K] [Finite K]
    (p:ℕ) [Fact p.Prime] [CharP K p] : Sylow p (fixedRootGenerated K (RingEquiv.refl K)) :=
  (positiveSylow K p).comapOfInjective (foldedEquiv K).toMonoidHom
    (foldedEquiv K).injective (by rw [MonoidHom.range_eq_top.mpr (foldedEquiv K).surjective];exact le_top)

private theorem positiveInGenerated_coe (K:Type) [Field K] [Finite K]
    (p:ℕ) [Fact p.Prime] [CharP K p] :
    (positiveInGenerated K p : Subgroup (fixedRootGenerated K (RingEquiv.refl K)))=
      rootPart K (RingEquiv.refl K) false := by
  ext x
  change foldedEquiv K x∈(positiveSylow K p : Subgroup (canonicalElementaryGroup realizationData K))↔_
  rw [positiveSylow_coe]
  constructor
  · intro hx
    exact ⟨hx,fixedRootGenerated_le_fixed K (RingEquiv.refl K) x.property⟩
  · intro hx
    exact hx.1

private theorem injective_subtype_of_eq {G H:Type*} [Group G] [Group H]
    (f:G→*H) (P Q:Subgroup G) (he:P=Q) (hi:Function.Injective (f.comp Q.subtype)) :
    Function.Injective (f.comp P.subtype) := by
  subst P
  exact hi

def originalPairNormalizer (K:Type) [Field K] [Finite K]
    (p:ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)] :
    Subgroup (Projective CartanMatrix.F₄ K) :=
  Subgroup.normalizer (originalPositiveSylow K p : Set (Projective CartanMatrix.F₄ K))⊓
    Subgroup.normalizer (originalNegative K : Set (Projective CartanMatrix.F₄ K))

theorem mem_originalPairNormalizer_iff (K:Type) [Field K] [Finite K]
    (p:ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)]
    (g:fixedRootGenerated K (RingEquiv.refl K)) :
    generatedToOriginal K g∈originalPairNormalizer K p↔
      g.val∈pairNormalizer K (RingEquiv.refl K) := by
  have hpinj : Function.Injective ((generatedToOriginal K).comp
      (positiveInGenerated K p : Subgroup (fixedRootGenerated K (RingEquiv.refl K))).subtype) :=
    injective_subtype_of_eq (generatedToOriginal K) _ _ (positiveInGenerated_coe K p)
      (rootPart_positive_original_injective K p)
  have hsign (neg:Bool) :
      generatedToOriginal K g∈Subgroup.normalizer
        ((rootPart K (RingEquiv.refl K) neg).map (generatedToOriginal K) :
          Set (Projective CartanMatrix.F₄ K))↔
      g.val∈Subgroup.normalizer (signedFixed K (RingEquiv.refl K) neg :
        Set (Matrix GeckIndex GeckIndex K)ˣ) := by
    rw [mem_normalizer_map_iff (generatedToOriginal K) (positiveInGenerated K p)
      hpinj (generatedToOriginal_kernel_le_center K p) _ (rootPart_isPGroup _ _ p neg)]
    change g∈Subgroup.normalizer ((signedFixed K (RingEquiv.refl K) neg).subgroupOf
      (fixedRootGenerated K (RingEquiv.refl K)) : Set _)↔_
    rw [←Subgroup.subgroupOf_normalizer_eq (signedFixed_le_generated _ _ neg)]
    rfl
  have hp := hsign false
  have hn := hsign true
  rw [rootPart_positive_original_image K p] at hp
  rw [rootPart_negative_original_image] at hn
  exact ⟨fun h=>⟨⟨hp.mp h.1,hn.mp h.2⟩,g.property⟩,
    fun h=>⟨hp.mpr h.1.1,hn.mpr h.1.2⟩⟩

theorem originalPairNormalizer_positive_scalars (K:Type) [Field K] [Finite K]
    (p:ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)]
    (d:Projective CartanMatrix.F₄ K) (hd:d∈originalPairNormalizer K p) :
    ∃c:Fin 4→Kˣ,∀i t,
      d*originalSimpleHom K false i (Multiplicative.ofAdd t)*d⁻¹=
        originalSimpleHom K false i (Multiplicative.ofAdd ((c i:K)*t)) := by
  obtain ⟨g,rfl⟩ := generatedToOriginal_surjective K d
  have hg := (mem_originalPairNormalizer_iff K p g).mp hd
  obtain ⟨c,hc⟩ := pairNormalizer_positive_scalars K g.val hg
  refine ⟨c,?_⟩
  intro i t
  have he : g*simpleInGenerated K false i (Multiplicative.ofAdd t)*g⁻¹=
      simpleInGenerated K false i (Multiplicative.ofAdd ((c i:K)*t)) := by
    apply Subtype.ext
    simpa only [Subgroup.coe_mul,Subgroup.coe_inv,simpleInGenerated_val] using hc i t
  simpa only [map_mul,map_inv,simpleInGenerated_original] using congrArg (generatedToOriginal K) he

end SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalPairScalarAction
