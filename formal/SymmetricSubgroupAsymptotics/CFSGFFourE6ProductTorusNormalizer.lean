import SymmetricSubgroupAsymptotics.CFSGFFourE6ProductTorus
import SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalRootIntersection
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootLineNormalizers

/-! Actual native product tori normalize both full original Sylow
subgroups. This uses whole ambient U/V normalization and twist fixedness,
not generation of folded U by only its simple positive charts. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6ProductTorusNormalizer
open CFSGFFourE6ProductTorus CFSGFFourE6GeneratedOriginalProjection
open CFSGFFourE6OriginalRootIntersection CFSGFFourE6OriginalOppositeAlignment
open CFSGFFourE6OriginalProjection CFSGTwistedE6GeckRelativeRootGenerated
open CFSGTwistedE6GeckRootGeneratedPGroup CFSGTwistedE6GeckDiagramCovariance
open CFSGTwistedE6GeckMatrixTwist CFSGTwistedE6GeckPositiveTwist
open CFSGNormTwoCoordinateRootLineNormalizers CFSGE6GeckProductTorus
open CFSGCentralTwistedCommutatorLift CFSGExceptionalCartanPositiveDefinite
open CFSG.Models.Chevalley

theorem productTorusGenerated_normalizes (K : Type) [Field K] (x : Fin 4→Kˣ) (neg : Bool) :
    productTorusGenerated K x∈Subgroup.normalizer
      (rootPart K (RingEquiv.refl K) neg : Set (fixedRootGenerated K (RingEquiv.refl K))) := by
  let J := fixedRootGenerated K (RingEquiv.refl K)
  let t := productTorusGenerated K x
  have ht : t.val∈Subgroup.normalizer
      (signedFixed K (RingEquiv.refl K) neg : Set (Matrix GeckIndex GeckIndex K)ˣ) := by
    apply Subgroup.inf_normalizer_le_normalizer_inf
    refine ⟨?_,?_⟩
    · change t.val∈Subgroup.normalizer (SignedUpper K neg : Set (Matrix GeckIndex GeckIndex K)ˣ)
      have htorus := rawProductTorus_mem_torus K (torusTuple K x)
      rw [←productTorusGenerated_val K x] at htorus
      exact torusGroup_normalizes CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
        E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K neg htorus
    · exact (fixedSubgroup (unitTwist K (RingEquiv.refl K))).le_normalizer
        (fixedRootGenerated_le_fixed K (RingEquiv.refl K) t.property)
  exact Subgroup.le_normalizer_comap J.subtype ht

theorem original_product_torus_rootPart (K : Type) [Field K] [Finite K]
    [IsSimpleGroup (Projective CartanMatrix.F₄ K)] (x : Fin 4→Kˣ) (neg : Bool) :
    ((rootPart K (RingEquiv.refl K) neg).map (generatedToOriginal K)).map
      (MulAut.conj (originalProductTorusHom K x)).toMonoidHom=
      (rootPart K (RingEquiv.refl K) neg).map (generatedToOriginal K) := by
  have hn := Subgroup.le_normalizer_map (generatedToOriginal K)
    ⟨productTorusGenerated K x,productTorusGenerated_normalizes K x neg,rfl⟩
  apply SetLike.coe_injective
  exact Subgroup.mem_normalizer_iff_conj_image_eq.mp hn

theorem original_product_torus_positive (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)] (x : Fin 4→Kˣ) :
    (originalPositiveSylow K p : Subgroup (Projective CartanMatrix.F₄ K)).map
      (MulAut.conj (originalProductTorusHom K x)).toMonoidHom=
      (originalPositiveSylow K p : Subgroup (Projective CartanMatrix.F₄ K)) := by
  simpa only [rootPart_positive_original_image K p] using original_product_torus_rootPart K x false

theorem original_product_torus_negative (K : Type) [Field K] [Finite K]
    [IsSimpleGroup (Projective CartanMatrix.F₄ K)] (x : Fin 4→Kˣ) :
    (originalNegative K).map (MulAut.conj (originalProductTorusHom K x)).toMonoidHom=originalNegative K := by
  simpa only [rootPart_negative_original_image] using original_product_torus_rootPart K x true

end SymmetricSubgroupAsymptotics.CFSGFFourE6ProductTorusNormalizer
