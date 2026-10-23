import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckRelativeWordEnvelope
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckNormalizerEnvelopeTwist
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckInversionParts
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylWordTorus

/-! Every genuinely fixed element of the literal E6 matrix group has
an enlarged-normalizer/inversion cell with a genuinely fixed relative
Weyl representative. The cover uses the proved finite U-intersection
factorization; no torus-kernel recognition or fixed-factor premise occurs. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckRelativeBruhatCover
open CFSGTwistedE6GeckDiagramCovariance CFSGExceptionalNormTwoBases
open CFSGExceptionalCartanPositiveDefinite CFSGTwistedE6WeylChamber
open CFSGTwistedE6FixedWordClassification CFSGTwistedE6GeckRelativeWordEnvelope
open CFSGTwistedE6GeckNormalizerEnvelope CFSGTwistedE6GeckNormalizerEnvelopeTwist
open CFSGTwistedE6GeckInversionParts CFSGNormTwoGeckWeylWordDegree
open CFSGTwistedE6GeckPositiveTwist
open CFSGNormTwoGeckIntegralWord CFSGNormTwoGeckBorelEnvelope
open CFSGNormTwoGeckBorelFactorization CFSGNormTwoGeckWeylWordTorus
open CFSGNormTwoCoordinateRootLineNormalizers
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos

theorem exists_relative_inversion_cell_of_commuting_word (K : Type) [Field K] [Finite K]
    (g b c : (Matrix GeckIndex GeckIndex K)ˣ) (w : List (Fin 6))
    (hb : b ∈ borelEnvelope A hs hp E6Base E6Index K)
    (hc : c ∈ borelEnvelope A hs hp E6Base E6Index K)
    (he : g = b * wordUnit A hs hp E6Base E6Index K w * c)
    (hcomm : ∀ k, diagramRoot (rootAction w k) = rootAction w (diagramRoot k)) :
    ∃ (r : List (Fin 4)) (b : (Matrix GeckIndex GeckIndex K)ˣ),
      b ∈ normalizerEnvelope K ∧ ∃ v : InversionPart K (expandRelative r),
        g = b * wordUnit A hs hp E6Base E6Index K (expandRelative r) *
          inversionEmbedding K (expandRelative r) v := by
  obtain ⟨r,d,hdD,hword⟩ := exists_relative_matrix_factor K w hcomm
  let W := wordUnit A hs hp E6Base E6Index K (expandRelative r)
  obtain ⟨u,hu,t,ht,hct⟩ := borel_factor A hs hp E6Base E6Index K c hc
  let up := t⁻¹*u*t
  have hup : up ∈ Positive K := by
    have htn := torusGroup_normalizes A hd hs hp ho K false
      ((torusGroup A hs hp E6Base E6Index K).inv_mem ht)
    have hh := (Subgroup.mem_normalizer_iff.mp htn u).mp hu
    simpa only [inv_inv] using hh
  have hct' : c = t*up := by
    rw [hct]
    dsimp only [up]
    group
  have ht' : W*t*W⁻¹ ∈ torusGroup A hs hp E6Base E6Index K :=
    (Subgroup.mem_normalizer_iff.mp
      (wordUnit_mem_torus_normalizer A hs hp E6Base E6Index K (expandRelative r)) t).mp ht
  let n := (b*d)*(W*t*W⁻¹)
  have hn : n ∈ normalizerEnvelope K :=
    (normalizerEnvelope K).mul_mem
      ((normalizerEnvelope K).mul_mem (borel_le_normalizerEnvelope K hb)
        (diagonalNormalizer_le_envelope K hdD))
      (diagonalNormalizer_le_envelope K (torus_le_diagonalNormalizer K ht'))
  have hgn : g = n*W*up := by
    rw [he,hword,hct']
    dsimp only [n,W]
    group
  obtain ⟨p,hpU,v,hprod⟩ := exists_positive_inversion_factors K (expandRelative r) ⟨up,hup⟩
  refine ⟨r,n*(W*p*W⁻¹),
    (normalizerEnvelope K).mul_mem hn (positive_le_envelope K hpU),v,?_⟩
  change g = (n*(W*p*W⁻¹))*W*inversionEmbedding K (expandRelative r) v
  calc
    g = n*W*up := hgn
    _ = n*W*(p*inversionEmbedding K (expandRelative r) v) := congrArg (fun x => n*W*x) hprod
    _ = _ := by group

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckRelativeBruhatCover
