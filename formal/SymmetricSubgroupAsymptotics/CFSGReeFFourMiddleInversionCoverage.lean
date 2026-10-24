import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleFixedLevi
import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleInversionSupport
import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalInversionFactors
import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleNegativeFamily
import SymmetricSubgroupAsymptotics.CFSGFFourOriginalPositiveDiagramImage

/-! Coverage of the literal original middle inversion subgroup by its
four original source parameters. Diagram-fixed functional-Levi generation
and injectivity of the SAME original hom prove coverage. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleInversionCoverage
open CFSG.Models.Chevalley CFSGFFourOriginalMiddleWords CFSGReeFFourFieldParameters
open CFSGReeFFourMiddleFixedWords CFSGReeFFourMiddleWordInjective
open CFSGReeFFourOriginalInversionFactors CFSGReeFFourRelativeSimpleWeyl
open CFSGReeFFourRelativeWeylRawWords CFSGReeFFourMiddleInversionSupport
open CFSGReeFFourMiddleFixedLevi CFSGReeFFourMiddlePositiveSubgroup
open CFSGFFourOriginalPositiveDiagramImage CFSGReeFFourMiddleNegativeFamily
open CFSGTwistedE6GeckPositiveTwist CFSGTwistedE6GeckMatrixTwist
open CFSGNormTwoGeckIntegralWord

theorem rawHom_mem_middleInversion (m : ℕ)
    (g : Model CartanMatrix.F₄ (Field m))
    (hg : g ∈ modelInversion m (middleRelativeWeyl m)) :
    rawHom (Field m) g ∈ middleInversion (Field m) := by
  refine ⟨hg.1,?_⟩
  have hn := hg.2
  change rawHom (Field m) (middleRelativeWeyl m*g*(middleRelativeWeyl m)⁻¹) ∈
    Negative (Field m) at hn
  rw [map_mul,map_mul,map_inv,rawHom_middleRelativeWeyl] at hn
  simpa only [blockWord,word_eq_canonicalWord] using hn

theorem exists_middle_parameters (m : ℕ)
    (g : Model CartanMatrix.F₄ (Field m))
    (hg : g ∈ modelInversion m (middleRelativeWeyl m)) :
    ∃ a b c d : Field m, middleWord m a b c d = g := by
  let u : Positive (Field m) := ⟨rawHom (Field m) g,hg.1⟩
  have hfixed : positiveTwist (Field m) (RingEquiv.refl (Field m)) u = u :=
    Subtype.ext (rawHom_diagram_fixed (Field m) g)
  have hpres := middleInversion_le_preserving (Field m) (rawHom_mem_middleInversion m g hg)
  have hu := fixed_preserving_mem_middle m u hfixed hpres
  obtain ⟨a,b,c,d,he⟩ := exists_source_middle_parameters m u hu
  exact ⟨a,b,c,d,rawHom_injective (Field m) he⟩

theorem middleWord_mem_inversion (m : ℕ) (a b c d : Field m) :
    middleWord m a b c d ∈ modelInversion m (middleRelativeWeyl m) := by
  constructor
  · change rawHom (Field m) (middleWord m a b c d) ∈ Positive (Field m)
    rw [rawHom_middleWord]
    exact (matrixMiddleWord (Field m) a b c d).property
  · exact rawHom_middle_conjugate_middleWord_mem_negative m a b c d

end SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleInversionCoverage
