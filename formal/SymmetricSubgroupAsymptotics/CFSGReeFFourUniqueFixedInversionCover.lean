import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedBorelCardinality
import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalEnvelopeFactors
import SymmetricSubgroupAsymptotics.CFSGOpposedSubgroupPeeling
import SymmetricSubgroupAsymptotics.CFSGUniqueBruhatDiagonalNormalizer

/-! The actual fixed Bruhat cover retains its inversion constraint,
and its U-D-word-inversion coordinates are injective. The two assertions
are transported from the same original Model, not from a word-action census. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourUniqueFixedInversionCover
open CFSGReeFFourFieldParameters CFSGReeFFourFixedModelEquivalence
open CFSGReeFFourFixedPositiveFamilies CFSGReeFFourOppositionFixedPositiveNegative
open CFSGReeFFourFixedBruhatCover CFSGReeFFourFixedBorelCardinality
open CFSGReeFFourUniqueInversionCells CFSGReeFFourOriginalEnvelopeFactors
open CFSGReeFFourOriginalInversionFactors CFSGReeFFourOriginalWeylWords
open CFSGReeFFourFixedWordClassification CFSGReeFFourAmbientPositiveStability
open CFSGReeFFourOriginalNegativeStability CFSGFFourOriginalAmbientHom
open CFSGOpposedSubgroupPeeling CFSGUniqueBruhatDiagonalNormalizer
open CFSGCentralTwistedProductCoordinates

theorem exists_fixed_inversion_four_factor_cell (m : ℕ) (g : originalModelFixed m) :
    ∃u∈fixedPositive m,∃d∈fixedDiagonal m,∃w : List Bool,
      ∃v∈inversionPart (fixedPositive m) (fixedNegative m) (fixedPairedWord m w),
        g=u*d*fixedPairedWord m w*v := by
  obtain ⟨b,hb,hbf,w,v,hv,hvf,hvn,he⟩ := exists_fixed_model_inversion_cell m g.val g.property
  obtain ⟨u,hu,huf,d,hd,hdf,hbd⟩ := exists_fixed_model_envelope_factors m b hb hbf
  let U : originalModelFixed m := ⟨u,huf⟩
  let D : originalModelFixed m := ⟨d,hdf⟩
  let V : originalModelFixed m := ⟨v,hvf⟩
  have hU : U∈fixedPositive m := by
    rw [fixedPositive_eq_model_comap]
    exact hu
  have hV : V∈fixedPositive m := by
    rw [fixedPositive_eq_model_comap]
    exact hv
  refine ⟨U,hU,D,hd,w,V,⟨hV,?_⟩,?_⟩
  · change modelWeylWord (Field m) (expandPaired w)*v*
      (modelWeylWord (Field m) (expandPaired w))⁻¹∈modelNegative m
    exact hvn
  · apply Subtype.ext
    change g.val=u*d*modelWeylWord (Field m) (expandPaired w)*v
    rw [he,hbd]

theorem fixed_inversion_factorMap_injective (m : ℕ) (W : originalModelFixed m) :
    Function.Injective (factorMap (fixedPositive m) (fixedDiagonal m)
      (inversionPart (fixedPositive m) (fixedNegative m) W) W) := by
  let R := inversionPart (fixedPositive m) (fixedNegative m) W
  have hB := shifted_product_factors_injective (fixedBorel m) (fixedNegative m) W
    R.subtype Subtype.val_injective (fixedBorel_negative_disjoint m) (fun v=>v.property.2)
  intro x y he
  let px : fixedBorel m×R := (borelProduct m (x.1,x.2.1),x.2.2)
  let py : fixedBorel m×R := (borelProduct m (y.1,y.2.1),y.2.2)
  have he' : px.1.val*W*px.2.val=py.1.val*W*py.2.val := he
  have hp : px=py := hB he'
  have hUD : (x.1,x.2.1)=(y.1,y.2.1) :=
    (borelProduct_bijective m).injective (congrArg Prod.fst hp)
  have hU : x.1=y.1 := congrArg (fun z : fixedPositive m×fixedDiagonal m=>z.1) hUD
  have hD : x.2.1=y.2.1 := congrArg (fun z : fixedPositive m×fixedDiagonal m=>z.2) hUD
  have hR : x.2.2=y.2.2 := congrArg (fun z : fixedBorel m×R=>z.2) hp
  exact Prod.ext hU (Prod.ext hD hR)

end SymmetricSubgroupAsymptotics.CFSGReeFFourUniqueFixedInversionCover
