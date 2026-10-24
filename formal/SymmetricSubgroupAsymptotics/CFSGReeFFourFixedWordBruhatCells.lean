import SymmetricSubgroupAsymptotics.CFSGReeFFourPairedModelWords

/-! A fixed original cell admits an actual exceptional-fixed paired word,
with its original diagonal-normalizer residual retained. Applying the
proved original cover gives an envelope-word-positive cell in the same
fixed original Model. The envelope and positive factors are not asserted
fixed here; that requires the subsequent unique-factor descent. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourFixedWordBruhatCells
open CFSG.Models.Chevalley CFSGReeFFourFieldParameters
open CFSGReeFFourOriginalAutomorphism CFSGReeFFourOriginalWeylWords
open CFSGReeFFourPairedModelWords CFSGReeFFourFixedWordClassification
open CFSGFFourOriginalBruhatCells CFSGFFourOriginalAmbientHom CFSGFFourOriginalMiddleWords

private theorem modelPositive_le_modelEnvelope (K : Type) [_root_.Field K] [Finite K] [CharP K 2] :
    modelPositive K≤modelEnvelope K := by
  intro x hx
  change rawHom K x∈CFSGTwistedE6GeckPositiveTwist.Positive K at hx
  change rawHom K x∈CFSGTwistedE6GeckNormalizerEnvelope.normalizerEnvelope K
  exact CFSGTwistedE6GeckNormalizerEnvelope.positive_le_envelope K hx

private theorem modelDiagonalPart_le_modelEnvelope (K : Type) [_root_.Field K] [Finite K]
    [CharP K 2] : modelDiagonalPart K≤modelEnvelope K := by
  intro x hx
  exact CFSGTwistedE6GeckNormalizerEnvelope.diagonalNormalizer_le_envelope K hx

theorem exists_fixed_cell_paired_word_residual (m : ℕ) (r : List (Fin 4))
    (b c : Model CartanMatrix.F₄ (Field m))
    (hb : b∈modelEnvelope (Field m)) (hc : c∈modelEnvelope (Field m))
    (hfix : reeAutomorphism m (b*modelWeylWord (Field m) r*c)=b*modelWeylWord (Field m) r*c) :
    ∃s : List Bool,∃d∈modelDiagonalPart (Field m),
      modelWeylWord (Field m) r=d*modelWeylWord (Field m) (expandPaired s) ∧
      reeAutomorphism m (modelWeylWord (Field m) (expandPaired s))=
        modelWeylWord (Field m) (expandPaired s) := by
  obtain ⟨s,hs⟩ := exists_fixed_cell_paired_action m r b c hb hc hfix
  refine ⟨s,modelWeylWord (Field m) r*(modelWeylWord (Field m) (expandPaired s))⁻¹,
    equal_action_model_residual_mem (Field m) r (expandPaired s) hs,?_,paired_model_word_fixed m s⟩
  group

theorem exists_fixed_model_paired_cell (m : ℕ) (g : Model CartanMatrix.F₄ (Field m))
    (hg : reeAutomorphism m g=g) :
    ∃b∈modelEnvelope (Field m),∃s : List Bool,∃v∈modelPositive (Field m),
      g=b*modelWeylWord (Field m) (expandPaired s)*v ∧
      reeAutomorphism m (modelWeylWord (Field m) (expandPaired s))=
        modelWeylWord (Field m) (expandPaired s) := by
  obtain ⟨u,hu,d,hdD,r,v,hv,he⟩ := exists_model_cell (Field m) g
  have hb : u*d∈modelEnvelope (Field m) :=
    (modelEnvelope (Field m)).mul_mem (modelPositive_le_modelEnvelope (Field m) hu)
      (modelDiagonalPart_le_modelEnvelope (Field m) hdD)
  have hvB : v∈modelEnvelope (Field m) := modelPositive_le_modelEnvelope (Field m) hv
  have hcellfix : reeAutomorphism m ((u*d)*modelWeylWord (Field m) r*v)=
      (u*d)*modelWeylWord (Field m) r*v := by
    rw [←he]
    exact hg
  obtain ⟨s,z,hz,hword,hsfix⟩ :=
    exists_fixed_cell_paired_word_residual m r (u*d) v hb hvB hcellfix
  refine ⟨(u*d)*z,(modelEnvelope (Field m)).mul_mem hb
    (modelDiagonalPart_le_modelEnvelope (Field m) hz),s,v,hv,?_,hsfix⟩
  rw [he,hword]
  group

end SymmetricSubgroupAsymptotics.CFSGReeFFourFixedWordBruhatCells
