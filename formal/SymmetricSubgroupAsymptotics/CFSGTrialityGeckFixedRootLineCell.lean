import SymmetricSubgroupAsymptotics.CFSGTrialityGeckRootLineBruhatCover
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckCentralTwistedCellFactors

/-! The tracked U/diagonal/inversion coordinates of a genuinely fixed
matrix are themselves fixed. The proof uses the two already proved
injective actual product charts and retains the root-line property. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedRootLineCell
open CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance
open CFSGTrialityRelativeWordLanguage CFSGTrialityGeckRootLineDiagonal
open CFSGTrialityGeckRootLineBruhatCover CFSGTrialityGeckNormalizerEnvelope
open CFSGTrialityGeckNormalizerEnvelopeTwist CFSGTrialityGeckMatrixTwist
open CFSGTrialityGeckPositiveTwist CFSGTrialityGeckSourceWordAction
open CFSGTrialityGeckBruhatCellFactors CFSGTrialityGeckCentralTwistedCellFactors
open CFSGTrialityGeckEnvelopeOppositeIntersection
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckIntegralWord
local notation "A" => CartanMatrix.D 4
local notation "hs" => CartanMatrix.D_transpose 4
local notation "hp" => D4_positive_definite

theorem exists_fixed_rootLine_cell (K : Type) [Field K] [Finite K]
    (sigma : K ≃+* K) (g : (Matrix GeckIndex GeckIndex K)ˣ)
    (hg : g ∈ MatrixGroup K) (hfixed : unitTwist K sigma g = g) :
    ∃ (r : List Bool) (u d : (Matrix GeckIndex GeckIndex K)ˣ),
      u ∈ Positive K ∧ unitTwist K sigma u = u ∧
      d ∈ rootLineDiagonal K ∧ unitTwist K sigma d = d ∧
      ∃ v : InversionPart K (expandRelative r),
        unitTwist K sigma (inversionEmbedding K (expandRelative r) v) =
          inversionEmbedding K (expandRelative r) v ∧
        g = (u*d) * wordUnit A hs hp Base Index K (expandRelative r) *
          inversionEmbedding K (expandRelative r) v := by
  obtain ⟨r,u,d,hu,hd,v,he⟩ := exists_rootLine_cell K sigma g hg hfixed
  have hdD := rootLineDiagonal_le_diagonal K hd
  have hb : u*d ∈ normalizerEnvelope K :=
    (normalizerEnvelope K).mul_mem (positive_le_envelope K hu)
      (diagonalNormalizer_le_envelope K hdD)
  have hW : unitTwist K sigma (wordUnit A hs hp Base Index K (expandRelative r)) =
      wordUnit A hs hp Base Index K (expandRelative r) := by
    simpa only [word_eq_canonicalWord] using relative_word_fixed K sigma r
  have hf : unitTwist K sigma ((u*d)*wordUnit A hs hp Base Index K (expandRelative r)*
      inversionEmbedding K (expandRelative r) v) =
      (1 : MatrixGroup K).val * ((u*d)*wordUnit A hs hp Base Index K (expandRelative r)*
        inversionEmbedding K (expandRelative r) v) := by
    simpa only [←he,Subgroup.coe_one,one_mul] using hfixed
  have hh := central_twisted_cell_coordinates K sigma (expandRelative r) hW 1
    (Subgroup.one_mem _) ⟨u*d,hb⟩ v hf
  have hbf : unitTwist K sigma (u*d) = u*d := by
    simpa only [Subgroup.coe_one,one_mul] using hh.1
  have htu : unitTwist K sigma u ∈ Positive K := by
    have hm : unitTwist K sigma u ∈ (Positive K).map (unitTwist K sigma).toMonoidHom :=
      ⟨u,hu,rfl⟩
    rwa [positive_twist_map] at hm
  have htd := diagonalNormalizer_twist_mem K sigma d hdD
  have hfactors := positive_diagonalNormalizer_factors_injective K
    (a₁ := (⟨unitTwist K sigma u,htu⟩,⟨unitTwist K sigma d,htd⟩))
    (a₂ := (⟨u,hu⟩,⟨d,hdD⟩)) (by
      change unitTwist K sigma u * unitTwist K sigma d = u*d
      rw [←map_mul]
      exact hbf)
  have huf : unitTwist K sigma u = u := congrArg (fun p => p.1.val) hfactors
  have hdf : unitTwist K sigma d = d := congrArg (fun p => p.2.val) hfactors
  exact ⟨r,u,d,hu,huf,hd,hdf,v,hh.2,he⟩

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedRootLineCell
