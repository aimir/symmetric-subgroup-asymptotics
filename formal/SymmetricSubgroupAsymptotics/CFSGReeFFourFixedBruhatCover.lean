import SymmetricSubgroupAsymptotics.CFSGReeFFourUniqueInversionCells
import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalEnvelopeFactors

/-! A genuine fixed four-factor cover in the SAME original F4 Model and
its exact fixed subgroup. Every positive, diagonal and paired-word factor
is actually Ree-fixed. The simultaneous-normalizer part is retained as
D; neither torus recognition nor generation nor a derived/centre quotient
identification is built into this cover, including at m=0. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourFixedBruhatCover
open CFSG.Models.Chevalley CFSGReeFFourFieldParameters CFSGReeFFourOriginalAutomorphism
open CFSGReeFFourUniqueInversionCells CFSGReeFFourOriginalEnvelopeFactors
open CFSGReeFFourOriginalWeylWords CFSGReeFFourFixedWordClassification
open CFSGReeFFourPairedModelWords CFSGReeFFourFixedModelEquivalence
open CFSGFFourOriginalBruhatCells CFSGFFourOriginalAmbientHom
open CFSGReeFFourFixedAmbientHom CFSGReeFFourAmbientPositiveStability
open CFSGReeFFourFixedPositiveFamilies

theorem exists_model_fixed_four_factor_cell (m : ℕ) (g : Model CartanMatrix.F₄ (Field m))
    (hg : reeAutomorphism m g=g) :
    ∃u∈modelPositive (Field m),reeAutomorphism m u=u ∧
      ∃d∈modelDiagonalPart (Field m),reeAutomorphism m d=d ∧
        ∃s : List Bool,∃v∈modelPositive (Field m),reeAutomorphism m v=v ∧
          g=u*d*modelWeylWord (Field m) (expandPaired s)*v := by
  obtain ⟨b,hb,hbf,s,v,hv,hvf,_hinversion,he⟩ := exists_fixed_model_inversion_cell m g hg
  obtain ⟨u,hu,huf,d,hd,hdf,hbval⟩ := exists_fixed_model_envelope_factors m b hb hbf
  refine ⟨u,hu,huf,d,hd,hdf,s,v,hv,hvf,?_⟩
  rw [he,hbval]

def fixedDiagonal (m : ℕ) : Subgroup (originalModelFixed m) :=
  (modelDiagonalPart (Field m)).comap (originalModelFixed m).subtype

def fixedPairedWord (m : ℕ) (s : List Bool) : originalModelFixed m :=
  ⟨modelWeylWord (Field m) (expandPaired s),paired_model_word_fixed m s⟩

theorem exists_fixed_four_factor_cell (m : ℕ) (g : originalModelFixed m) :
    ∃u∈fixedPositive m,∃d∈fixedDiagonal m,∃s : List Bool,∃v∈fixedPositive m,
      g=u*d*fixedPairedWord m s*v := by
  obtain ⟨u,hu,huf,d,hd,hdf,s,v,hv,hvf,he⟩ :=
    exists_model_fixed_four_factor_cell m g.val g.property
  let U : originalModelFixed m := ⟨u,huf⟩
  let D : originalModelFixed m := ⟨d,hdf⟩
  let V : originalModelFixed m := ⟨v,hvf⟩
  have hU : U∈fixedPositive m := by
    rw [fixedPositive_eq_model_comap]
    exact hu
  have hV : V∈fixedPositive m := by
    rw [fixedPositive_eq_model_comap]
    exact hv
  refine ⟨U,hU,D,hd,s,V,hV,?_⟩
  apply Subtype.ext
  exact he

end SymmetricSubgroupAsymptotics.CFSGReeFFourFixedBruhatCover
