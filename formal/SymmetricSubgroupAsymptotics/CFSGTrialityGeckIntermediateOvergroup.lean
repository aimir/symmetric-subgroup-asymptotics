import SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedUpperNormalizer
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckOvergroupWeylExtraction
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedRootLineCell

/-! Every strict overgroup of the intrinsic fixed upper normalizer in
an actual intermediate fixed matrix group contains one of the two
literal relative simple Weyl words. The fixed-cell decomposition and
parameter-one extraction are proved dependencies, not BN-pair inputs. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckIntermediateOvergroup
open CFSGTrialityGeckFixedUpperNormalizer CFSGTrialityGeckOvergroupWeylExtraction
open CFSGTrialityGeckFixedRootLineCell CFSGTrialityGeckBruhatCellFactors
open CFSGTrialityGeckRootLineDiagonal CFSGTrialityGeckNormalizerEnvelope
open CFSGTrialityGeckRelativeRootGenerated CFSGTrialityGeckPositiveTwist
open CFSGTrialityGeckDiagramCovariance CFSGTrialityD4NormTwo CFSGTrialityRelativeWordLanguage
open CFSGTrialityD4WordDiscriminant CFSGTrialityGeckSimpleOrbitFlags
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckIntegralWord
open CFSGSerreQuadraticWeylWord
local notation "A" => CartanMatrix.D 4
local notation "hs" => CartanMatrix.D_transpose 4
local notation "hp" => D4_positive_definite
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots A) := Classical.decEq _

theorem exists_simple_weyl_mem_of_upperIn_lt (K : Type) [Field K] [Finite K]
    (sigma : K ≃+* K) (L H : Subgroup (Matrix GeckIndex GeckIndex K)ˣ)
    (hJL : fixedRootGenerated K sigma ≤ L) (hL : L ≤ fixedRaw K sigma)
    (hBH : upperIn K L < H) (hHL : H ≤ L) :
    ∃ a : Bool, canonicalWord rawData K (orbitWord a) ∈ H := by
  obtain ⟨x,hxH,hxB⟩ := SetLike.exists_of_lt hBH
  have hxL := hL (hHL hxH)
  obtain ⟨r,u,d,hu,huf,hdiag,hdf,v,hvf,he⟩ :=
    exists_fixed_rootLine_cell K sigma x hxL.1 hxL.2
  let b := u*d
  let W := wordUnit A hs hp Base Index K (expandRelative r)
  let V := inversionEmbedding K (expandRelative r) v
  have hex : x = b*W*V := he
  have hb : b ∈ normalizerEnvelope K :=
    (normalizerEnvelope K).mul_mem (positive_le_envelope K hu)
      (diagonalNormalizer_le_envelope K (rootLineDiagonal_le_diagonal K hdiag))
  have hU : signedFixed K sigma false ≤ upperIn K L :=
    le_inf (inf_le_left.trans (positive_le_envelope K))
      ((signedFixed_le_generated K sigma false).trans hJL)
  have hvU : V ∈ signedFixed K sigma false := ⟨v.val.property,hvf⟩
  have hvH : V ∈ H := hBH.le (hU hvU)
  have hWL : W ∈ L := hJL (relativeWord_mem_generated K sigma r)
  have hbL : b ∈ L := by
    have hh := L.mul_mem (L.mul_mem (hHL hxH) (L.inv_mem (hU hvU).2)) (L.inv_mem hWL)
    have hc : x*V⁻¹*W⁻¹ = b := by rw [hex]; group
    exact hc ▸ hh
  have hbH : b ∈ H := hBH.le ⟨hb,hbL⟩
  have hWH : W ∈ H := by
    have hh := H.mul_mem (H.mul_mem (H.inv_mem hbH) hxH) (H.inv_mem hvH)
    have hc : b⁻¹*x*V⁻¹ = W := by rw [hex]; group
    exact hc ▸ hh
  have hne : linearAction (expandRelative r) ≠ 1 := by
    intro hi
    apply hxB
    refine ⟨?_,hHL hxH⟩
    rw [hex]
    exact (normalizerEnvelope K).mul_mem
      ((normalizerEnvelope K).mul_mem hb
        (diagonalNormalizer_le_envelope K (rootLineDiagonal_le_diagonal K
          (identity_word_mem_rootLineDiagonal K (expandRelative r) hi))))
      (positive_le_envelope K hvU.1)
  exact exists_simple_weyl_mem K sigma H (hU.trans hBH.le) r hWH hne

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckIntermediateOvergroup
