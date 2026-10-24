import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalInversionFactors
import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedWordBruhatCells
import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalPositiveNormalizer

/-! Original enlarged-envelope/inversion coordinates are injective. The
actual Ree automorphism preserves both coordinate spaces when the word
is fixed, so a fixed original group element has genuinely fixed factors.
This descends coordinates by uniqueness, not by fixed-point surjectivity. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourUniqueInversionCells
open CFSG.Models.Chevalley CFSGReeFFourFieldParameters
open CFSGReeFFourOriginalAutomorphism CFSGReeFFourOriginalWeylWords
open CFSGReeFFourOriginalInversionFactors CFSGReeFFourFixedWordBruhatCells
open CFSGReeFFourOriginalNegativeStability CFSGReeFFourOriginalPositiveNormalizer
open CFSGFFourOriginalBruhatCells CFSGFFourOriginalAmbientHom CFSGFFourOriginalMiddleWords
open CFSGReeFFourFixedWordClassification CFSGCentralTwistedProductCoordinates

theorem modelEnvelope_negative_disjoint (m : ℕ) :
    Disjoint (modelEnvelope (Field m)) (modelNegative m) := by
  apply Subgroup.disjoint_def.mpr
  intro x hx hn
  have hraw : rawHom (Field m) x=1 := Subgroup.disjoint_def.mp
    (CFSGTwistedE6GeckCentralTwistedCellFactors.envelope_negative_disjoint (Field m)) hx hn
  apply rawHom_injective (Field m)
  simpa only [map_one] using hraw

theorem model_envelope_inversion_factors_injective (m : ℕ)
    (W : Model CartanMatrix.F₄ (Field m)) :
    Function.Injective (fun z : modelEnvelope (Field m) × modelInversion m W=>
      z.1.val*W*z.2.val) := by
  apply shifted_product_factors_injective (modelEnvelope (Field m)) (modelNegative m) W
    (modelInversion m W).subtype Subtype.val_injective (modelEnvelope_negative_disjoint m)
  intro v
  exact v.property.2

theorem fixed_original_inversion_cell_coordinates (m : ℕ)
    (W : Model CartanMatrix.F₄ (Field m)) (hW : reeAutomorphism m W=W)
    (b : modelEnvelope (Field m)) (v : modelInversion m W)
    (hfix : reeAutomorphism m (b.val*W*v.val)=b.val*W*v.val) :
    reeAutomorphism m b.val=b.val ∧ reeAutomorphism m v.val=v.val := by
  have hbt : reeAutomorphism m b.val∈modelEnvelope (Field m) := by
    have h : reeAutomorphism m b.val∈(modelEnvelope (Field m)).map (reeAutomorphism m).toMonoidHom :=
      ⟨b.val,b.property,rfl⟩
    rwa [ree_preserves_modelEnvelope] at h
  let bt : modelEnvelope (Field m) := ⟨reeAutomorphism m b.val,hbt⟩
  let vt : modelInversion m W :=
    ⟨reeAutomorphism m v.val,modelInversion_twist_mem m W hW v.val v.property⟩
  have hp : bt.val*W*vt.val=b.val*W*v.val := by
    change reeAutomorphism m b.val*W*reeAutomorphism m v.val=b.val*W*v.val
    simpa only [map_mul,hW] using hfix
  have he := model_envelope_inversion_factors_injective m W (a₁ := (bt,vt)) (a₂ := (b,v)) hp
  exact ⟨congrArg (fun z : modelEnvelope (Field m) × modelInversion m W=>z.1.val) he,
    congrArg (fun z : modelEnvelope (Field m) × modelInversion m W=>z.2.val) he⟩

theorem exists_fixed_model_inversion_cell (m : ℕ) (g : Model CartanMatrix.F₄ (Field m))
    (hg : reeAutomorphism m g=g) :
    ∃b∈modelEnvelope (Field m),reeAutomorphism m b=b ∧ ∃s : List Bool,
      ∃v∈modelPositive (Field m),reeAutomorphism m v=v ∧
        modelWeylWord (Field m) (expandPaired s)*v*
          (modelWeylWord (Field m) (expandPaired s))⁻¹∈modelNegative m ∧
        g=b*modelWeylWord (Field m) (expandPaired s)*v := by
  obtain ⟨b,hb,s,u,hu,he,hW⟩ := exists_fixed_model_paired_cell m g hg
  obtain ⟨p,hp,v,hv,hprod,hpW⟩ := exists_model_positive_sign_factors m (expandPaired s) u hu
  let W := modelWeylWord (Field m) (expandPaired s)
  let b' := b*(W*p*W⁻¹)
  have hpB : W*p*W⁻¹∈modelEnvelope (Field m) := by
    change rawHom (Field m) (W*p*W⁻¹)∈
      CFSGTwistedE6GeckNormalizerEnvelope.normalizerEnvelope (Field m)
    exact CFSGTwistedE6GeckNormalizerEnvelope.positive_le_envelope (Field m) hpW
  have hb' : b'∈modelEnvelope (Field m) := (modelEnvelope (Field m)).mul_mem hb hpB
  have he' : g=b'*W*v := by
    rw [he,hprod]
    dsimp only [b',W]
    group
  have hfix : reeAutomorphism m (b'*W*v)=b'*W*v := by
    rw [←he']
    exact hg
  have hcoords := fixed_original_inversion_cell_coordinates m W hW ⟨b',hb'⟩ ⟨v,hv⟩ hfix
  exact ⟨b',hb',hcoords.1,s,v,hv.1,hcoords.2,hv.2,he'⟩

end SymmetricSubgroupAsymptotics.CFSGReeFFourUniqueInversionCells
