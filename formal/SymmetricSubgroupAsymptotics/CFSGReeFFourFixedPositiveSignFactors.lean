import SymmetricSubgroupAsymptotics.CFSGReeFFourUniqueInversionCells

/-! Both actual positive sign factors of an exceptional-fixed element
are fixed when the literal word is fixed. This is a consequence of the
checked original envelope/inversion uniqueness, not fixed-point lifting. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourFixedPositiveSignFactors
open CFSG.Models.Chevalley CFSGReeFFourFieldParameters
open CFSGReeFFourOriginalAutomorphism CFSGReeFFourOriginalWeylWords
open CFSGReeFFourOriginalInversionFactors CFSGReeFFourUniqueInversionCells
open CFSGFFourOriginalBruhatCells CFSGFFourOriginalAmbientHom CFSGFFourOriginalMiddleWords

theorem exists_fixed_positive_sign_factors (m : ℕ) (r : List (Fin 4))
    (hW : reeAutomorphism m (modelWeylWord (Field m) r) = modelWeylWord (Field m) r)
    (u : Model CartanMatrix.F₄ (Field m)) (hu : u∈modelPositive (Field m))
    (hfixed : reeAutomorphism m u=u) :
    ∃ p∈modelPositive (Field m), reeAutomorphism m p=p ∧
      ∃ v∈modelInversion m (modelWeylWord (Field m) r), reeAutomorphism m v=v ∧
        u=p*v ∧ modelWeylWord (Field m) r*p*(modelWeylWord (Field m) r)⁻¹∈
          modelPositive (Field m) := by
  obtain ⟨p,hp,v,hv,hprod,hpW⟩ := exists_model_positive_sign_factors m r u hu
  let W := modelWeylWord (Field m) r
  have hWlocal : reeAutomorphism m W=W := hW
  let b := W*p*W⁻¹
  have hb : b∈modelEnvelope (Field m) := by
    change rawHom (Field m) b ∈
      CFSGTwistedE6GeckNormalizerEnvelope.normalizerEnvelope (Field m)
    exact CFSGTwistedE6GeckNormalizerEnvelope.positive_le_envelope (Field m) hpW
  have he : b*W*v = W*u := by
    dsimp only [b]
    rw [hprod]
    group
  have hfix : reeAutomorphism m (b*W*v) = b*W*v := by
    rw [he,map_mul,hWlocal,hfixed]
  have hc := fixed_original_inversion_cell_coordinates m W hWlocal ⟨b,hb⟩ ⟨v,hv⟩ hfix
  have hpfixed : reeAutomorphism m p=p := by
    apply (MulAut.conj W).injective
    change W*reeAutomorphism m p*W⁻¹ = W*p*W⁻¹
    have h := hc.1
    change reeAutomorphism m (W*p*W⁻¹) = W*p*W⁻¹ at h
    simpa only [map_mul,map_inv,hWlocal] using h
  exact ⟨p,hp,hpfixed,v,hv,hc.2,hprod,hpW⟩

end SymmetricSubgroupAsymptotics.CFSGReeFFourFixedPositiveSignFactors
