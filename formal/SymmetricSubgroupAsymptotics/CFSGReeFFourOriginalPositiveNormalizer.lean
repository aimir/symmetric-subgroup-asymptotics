import SymmetricSubgroupAsymptotics.CFSGFFourOriginalBruhatCells
import SymmetricSubgroupAsymptotics.CFSGReeFFourAmbientPositiveStability

/-! The enlarged raw envelope inside the SAME original Model is its
literal positive normalizer. Ambient regular uniqueness proves the
reverse inclusion. Thus the actual exceptional automorphism preserves
this whole envelope, without a positive-generator or torus assertion. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalPositiveNormalizer
open CFSG.Models.Chevalley CFSGReeFFourFieldParameters
open CFSGReeFFourOriginalAutomorphism CFSGReeFFourRegularFixedPositive
open CFSGReeFFourFixedAmbientHom CFSGFFourOriginalMiddleWords
open CFSGFFourOriginalAmbientHom CFSGFFourOriginalBruhatCells
open CFSGReeFFourAmbientPositiveStability CFSGFFourE6AmbientPositiveSylow
open CFSGRegularElementSylowPreimage CFSGTwistedE6GeckPositiveTwist
open CFSGTwistedE6GeckNormalizerEnvelope
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem modelEnvelope_eq_positive_normalizer (m : ℕ) :
    modelEnvelope (Field m)=Subgroup.normalizer
      (modelPositive (Field m) : Set (Model CartanMatrix.F₄ (Field m))) := by
  apply le_antisymm
  · intro g hg
    have hn : rawHom (Field m) g∈Subgroup.normalizer
        (Positive (Field m) : Set (Matrix CFSGFFourSerreMatrices.Index
          CFSGFFourSerreMatrices.Index (Field m))ˣ) := hg.1
    change g∈Subgroup.normalizer (((Positive (Field m)).comap (rawHom (Field m))) :
      Set (Model CartanMatrix.F₄ (Field m)))
    exact Subgroup.le_normalizer_comap (rawHom (Field m)) hn
  · intro g hg
    have hnA := preimage_normalizer_le_comap_normalizer (ambientSylow (Field m) 2)
      (modelAmbientHom (Field m)) (regularFixed m).val
      (fixedAmbientHom_regular_positive m) (fixedAmbientHom_regular_unique m) hg
    have hnRaw := CFSGTwistedE6GeckAmbientPositiveSylow.ambient_normalizer_map_le (Field m)
      ⟨modelAmbientHom (Field m) g,hnA,rfl⟩
    exact hnRaw

theorem ree_preserves_modelEnvelope (m : ℕ) :
    (modelEnvelope (Field m)).map (reeAutomorphism m).toMonoidHom=modelEnvelope (Field m) := by
  rw [modelEnvelope_eq_positive_normalizer]
  exact (Subgroup.map_equiv_normalizer_eq (modelPositive (Field m)) (reeAutomorphism m)).trans
    (congrArg (fun S : Subgroup (Model CartanMatrix.F₄ (Field m))=>
      Subgroup.normalizer (S : Set (Model CartanMatrix.F₄ (Field m))))
      (ree_preserves_modelPositive m))

end SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalPositiveNormalizer
