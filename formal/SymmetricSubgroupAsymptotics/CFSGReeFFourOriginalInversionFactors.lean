import SymmetricSubgroupAsymptotics.CFSGFFourOriginalPositiveDiagramImage
import SymmetricSubgroupAsymptotics.CFSGE6GeckFixedPositiveInversionFactors
import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalNegativeStability

/-! Original positive factors split along an actual original word into
its positive and negative sign parts. Diagram-fixedness and the proved
original image equivalence produce the factors. The negative sign part
is intrinsically preserved by the actual Ree automorphism whenever the
original word is fixed. No fixed-point lift through Ree T is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalInversionFactors
open CFSG.Models.Chevalley CFSGReeFFourFieldParameters
open CFSGReeFFourOriginalAutomorphism CFSGReeFFourOriginalWeylWords
open CFSGReeFFourOriginalNegativeStability CFSGReeFFourAmbientPositiveStability
open CFSGFFourOriginalAmbientHom CFSGFFourOriginalMiddleWords
open CFSGFFourOriginalPositiveDiagramImage CFSGE6GeckFixedPositiveInversionFactors
open CFSGTwistedE6GeckDiagramCovariance CFSGTwistedE6GeckInversionParts
open CFSGTwistedE6FixedWordClassification CFSGNormTwoGeckIntegralWord

def modelInversion (m : ℕ) (W : Model CartanMatrix.F₄ (Field m)) :
    Subgroup (Model CartanMatrix.F₄ (Field m)) :=
  modelPositive (Field m) ⊓ (modelNegative m).comap (MulAut.conj W).toMonoidHom

theorem exists_model_positive_sign_factors (m : ℕ) (r : List (Fin 4))
    (u : Model CartanMatrix.F₄ (Field m)) (hu : u∈modelPositive (Field m)) :
    ∃p∈modelPositive (Field m),∃v∈modelInversion m (modelWeylWord (Field m) r),
      u=p*v ∧ modelWeylWord (Field m) r*p*(modelWeylWord (Field m) r)⁻¹∈modelPositive (Field m) := by
  have huraw : rawHom (Field m) u∈CFSGTwistedE6GeckPositiveTwist.Positive (Field m) := hu
  let uraw : CFSGTwistedE6GeckPositiveTwist.Positive (Field m) := ⟨rawHom (Field m) u,huraw⟩
  obtain ⟨praw,hpfix,vraw,hvfix,hprod,hpW⟩ := exists_fixed_positive_inversion_factors
    (Field m) (RingEquiv.refl (Field m)) r uraw (rawHom_diagram_fixed (Field m) u)
  obtain ⟨p,hp,hpraw⟩ := exists_modelPositive_of_diagram_fixed (Field m) praw hpfix.1 hpfix.2
  obtain ⟨v,hv,hvraw⟩ := exists_modelPositive_of_diagram_fixed (Field m)
    (inversionEmbedding (Field m) (expandRelative r) vraw) hvfix.1 hvfix.2
  refine ⟨p,hp,v,⟨hv,?_⟩,?_,?_⟩
  · change rawHom (Field m)
      (modelWeylWord (Field m) r*v*(modelWeylWord (Field m) r)⁻¹)∈
        CFSGTwistedE6GeckPositiveTwist.Negative (Field m)
    simp only [map_mul,map_inv,rawHom_modelWeylWord_relative,hvraw]
    simpa only [word_eq_canonicalWord] using vraw.property
  · apply rawHom_injective (Field m)
    simp only [map_mul,hpraw,hvraw]
    exact hprod
  · change rawHom (Field m)
      (modelWeylWord (Field m) r*p*(modelWeylWord (Field m) r)⁻¹)∈
        CFSGTwistedE6GeckPositiveTwist.Positive (Field m)
    simp only [map_mul,map_inv,rawHom_modelWeylWord_relative,hpraw]
    exact hpW

theorem modelInversion_twist_mem (m : ℕ) (W : Model CartanMatrix.F₄ (Field m))
    (hW : reeAutomorphism m W=W) (v : Model CartanMatrix.F₄ (Field m))
    (hv : v∈modelInversion m W) : reeAutomorphism m v∈modelInversion m W := by
  have hpos : reeAutomorphism m v∈modelPositive (Field m) := by
    have h : reeAutomorphism m v∈(modelPositive (Field m)).map (reeAutomorphism m).toMonoidHom :=
      ⟨v,hv.1,rfl⟩
    rwa [ree_preserves_modelPositive] at h
  have hconj : W*v*W⁻¹∈modelNegative m := hv.2
  have hneg : reeAutomorphism m (W*v*W⁻¹)∈modelNegative m := by
    have h : reeAutomorphism m (W*v*W⁻¹)∈(modelNegative m).map (reeAutomorphism m).toMonoidHom :=
      ⟨W*v*W⁻¹,hconj,rfl⟩
    rwa [ree_preserves_modelNegative] at h
  refine ⟨hpos,?_⟩
  change W*reeAutomorphism m v*W⁻¹∈modelNegative m
  simpa only [map_mul,map_inv,hW] using hneg

end SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalInversionFactors
