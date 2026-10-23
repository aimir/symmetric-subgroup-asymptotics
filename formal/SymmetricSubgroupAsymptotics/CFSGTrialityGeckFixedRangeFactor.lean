import SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedRangePreimage
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckCentralTwistedBruhatCell
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckCentralTwistedCellFactors
import SymmetricSubgroupAsymptotics.CFSGCommutatorOfCommutativeFactor

/-! The full preimage of the fixed original action range factors as a
genuinely fixed-root-generated element times a diagonal element. Its
entire commutator therefore belongs to the fixed-root-generated part.
The diagonal coordinate may be centrally twisted; it is not assumed fixed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedRangeFactor
open CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance
open CFSGTrialityGeckFixedRangePreimage CFSGTrialityGeckRelativeRootGenerated
open CFSGTrialityGeckCentralTwistedBruhatCell CFSGTrialityGeckCentralTwistedCellFactors
open CFSGTrialityGeckMatrixTwist CFSGTrialityGeckNormalizerEnvelope
open CFSGTrialityGeckBruhatCellFactors CFSGTrialityRelativeWordLanguage
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckIntegralWord
open CFSGCommutatorOfCommutativeFactor
local notation "A" => CartanMatrix.D 4
local notation "hs" => CartanMatrix.D_transpose 4
local notation "hp" => D4_positive_definite

theorem fixed_range_preimage_factor (K : Type) [Field K] [Finite K] (sigma : K ≃+* K)
    (x : (Matrix GeckIndex GeckIndex K)ˣ) (hx : x ∈ ambientFixedRangePreimage K sigma) :
    ∃ j ∈ fixedRootGenerated K sigma, ∃ d ∈ diagonalNormalizer K, x = j*d := by
  obtain ⟨g,hg,rfl⟩ := hx
  have hLg : g.val ∈ ambientFixedRangePreimage K sigma := ⟨g,hg,rfl⟩
  obtain ⟨z,hz,hτ⟩ := preimage_central_twist K sigma g hg
  obtain ⟨r,b,hb,v,he⟩ := exists_central_twisted_relative_cell K sigma g.val g.property z hz hτ
  let W := wordUnit A hs hp Base Index K (expandRelative r)
  have hW : unitTwist K sigma W = W := by
    dsimp only [W]
    simpa only [word_eq_canonicalWord] using relative_word_fixed K sigma r
  have hcell : unitTwist K sigma (b*W*inversionEmbedding K (expandRelative r) v) =
      z.val*(b*W*inversionEmbedding K (expandRelative r) v) := by
    calc
      _ = unitTwist K sigma g.val := congrArg (unitTwist K sigma) he.symm
      _ = z.val*g.val := hτ
      _ = _ := congrArg (fun y => z.val*y) he
  have hc := central_twisted_cell_coordinates K sigma (expandRelative r) hW z hz ⟨b,hb⟩ v hcell
  obtain ⟨u,hu,hufix,d,hd,hdfix,hbprod⟩ :=
    exists_central_twisted_envelope_factors K sigma b hb z hz hc.1
  have huJ : u ∈ fixedRootGenerated K sigma :=
    signedFixed_le_generated K sigma false ⟨hu,hufix⟩
  have hvJ : inversionEmbedding K (expandRelative r) v ∈ fixedRootGenerated K sigma :=
    signedFixed_le_generated K sigma false ⟨v.val.property,hc.2⟩
  have hWV : W*inversionEmbedding K (expandRelative r) v ∈ fixedRootGenerated K sigma :=
    (fixedRootGenerated K sigma).mul_mem (relativeWord_mem_generated K sigma r) hvJ
  have hprod : g.val = u*d*W*inversionEmbedding K (expandRelative r) v :=
    he.trans (congrArg (fun y => y*W*inversionEmbedding K (expandRelative r) v) hbprod)
  have hdL : d ∈ ambientFixedRangePreimage K sigma := by
    have hh := (ambientFixedRangePreimage K sigma).mul_mem
      ((ambientFixedRangePreimage K sigma).mul_mem
        ((ambientFixedRangePreimage K sigma).inv_mem (fixedRootGenerated_le_preimage K sigma huJ)) hLg)
      ((ambientFixedRangePreimage K sigma).inv_mem (fixedRootGenerated_le_preimage K sigma hWV))
    have heD : u⁻¹*g.val*(W*inversionEmbedding K (expandRelative r) v)⁻¹ = d := by
      rw [hprod]
      group
    rwa [heD] at hh
  have hdN := diagonal_preimage_normalizes_generated K sigma ⟨hd,hdL⟩
  have hconj : d*(W*inversionEmbedding K (expandRelative r) v)*d⁻¹ ∈ fixedRootGenerated K sigma :=
    (Subgroup.mem_normalizer_iff.mp hdN _).mp hWV
  refine ⟨u*(d*(W*inversionEmbedding K (expandRelative r) v)*d⁻¹),
    (fixedRootGenerated K sigma).mul_mem huJ hconj,d,hd,?_⟩
  change g.val = u*(d*(W*inversionEmbedding K (expandRelative r) v)*d⁻¹)*d
  rw [hprod]
  group

theorem preimage_commutator_map_le_generated (K : Type) [Field K] [Finite K] (sigma : K ≃+* K) :
    (commutator (ambientFixedRangePreimage K sigma)).map
      (ambientFixedRangePreimage K sigma).subtype ≤ fixedRootGenerated K sigma := by
  apply commutator_map_le_of_factor (ambientFixedRangePreimage K sigma)
    (fixedRootGenerated K sigma) (diagonalNormalizer K)
    (fixedRootGenerated_le_preimage K sigma) (diagonal_preimage_normalizes_generated K sigma)
  · intro d hd e he
    exact congrArg (fun y : diagonalNormalizer K => y.val)
      (diagonalNormalizer_commute K ⟨d,hd⟩ ⟨e,he⟩).eq
  · exact fixed_range_preimage_factor K sigma

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedRangeFactor
