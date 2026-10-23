import SymmetricSubgroupAsymptotics.CFSGTrialityGeckRelativeWordEnvelope
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckNormalizerEnvelopeTwist
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedBruhatCell
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckBruhatCellFactors
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylWordTorus

/-! Every genuinely fixed element of the literal D4 matrix group has
an enlarged-normalizer/inversion cell with a genuinely fixed relative
Weyl representative. The cover uses the proved finite U-intersection
factorization; no torus-kernel recognition or fixed-factor premise occurs. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckRelativeBruhatCover
open CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance
open CFSGTrialityRelativeWordLanguage CFSGTrialityGeckRelativeWordEnvelope
open CFSGTrialityD4InvariantRoots CFSGTrialityD4WordDiscriminant
open CFSGTrialityGeckNormalizerEnvelope CFSGTrialityGeckNormalizerEnvelopeTwist
open CFSGTrialityGeckFixedBruhatCell CFSGTrialityGeckBruhatCellFactors
open CFSGTrialityGeckMatrixTwist CFSGTrialityGeckPositiveTwist
open CFSGNormTwoCoordinateWeylIntersectionFactor CFSGNormTwoCoordinateRootHeightQuotient
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckIntegralWord
open CFSGNormTwoGeckBorelEnvelope CFSGNormTwoGeckBorelFactorization
open CFSGNormTwoGeckWeylWordTorus CFSGNormTwoCoordinateRootLineNormalizers
local notation "A" => CartanMatrix.D 4
local notation "hd" => CartanMatrix.D_diag 4
local notation "hs" => CartanMatrix.D_transpose 4
local notation "hp" => D4_positive_definite
local notation "ho" => CartanMatrix.D_off_diag_nonpos 4

theorem exists_positive_inversion_factors (K : Type) [Field K] [Finite K]
    (w : List (Fin 4)) (u : Positive K) :
    ∃ p : (Matrix GeckIndex GeckIndex K)ˣ,
      wordUnit A hs hp Base Index K w*p*(wordUnit A hs hp Base Index K w)⁻¹ ∈ Positive K ∧
      ∃ v : InversionPart K w, u.val = p*inversionEmbedding K w v := by
  let up : PositiveGroup A hd hs hp ho K := ⟨u.val,u.property⟩
  obtain ⟨z,hz⟩ := (word_parts_product_bijective A hd hs hp ho K w).surjective up
  let p : (Matrix GeckIndex GeckIndex K)ˣ := z.1.val.val
  let v : InversionPart K w := z.2
  have he : p*inversionEmbedding K w v = u.val :=
    congrArg (fun x : PositiveGroup A hd hs hp ho K =>
      (x.val : (Matrix GeckIndex GeckIndex K)ˣ)) hz
  refine ⟨p,?_,v,he.symm⟩
  rw [word_eq_canonicalWord]
  exact z.1.property

theorem exists_relative_inversion_cell_of_commuting_word (K : Type) [Field K] [Finite K]
    (g b c : (Matrix GeckIndex GeckIndex K)ˣ) (w : List (Fin 4))
    (hb : b ∈ borelEnvelope A hs hp Base Index K)
    (hc : c ∈ borelEnvelope A hs hp Base Index K)
    (he : g = b * wordUnit A hs hp Base Index K w * c)
    (hcomm : ∀ k, diagramRoot (rootAction w k) = rootAction w (diagramRoot k)) :
    ∃ (r : List Bool) (b : (Matrix GeckIndex GeckIndex K)ˣ),
      b ∈ normalizerEnvelope K ∧ ∃ v : InversionPart K (expandRelative r),
        g = b * wordUnit A hs hp Base Index K (expandRelative r) *
          inversionEmbedding K (expandRelative r) v := by
  obtain ⟨r,d,hdD,hword⟩ := exists_relative_matrix_factor K w hcomm
  let W := wordUnit A hs hp Base Index K (expandRelative r)
  obtain ⟨u,hu,t,ht,hct⟩ := borel_factor A hs hp Base Index K c hc
  let up := t⁻¹*u*t
  have hup : up ∈ Positive K := by
    have htn := torusGroup_normalizes A hd hs hp ho K false
      ((torusGroup A hs hp Base Index K).inv_mem ht)
    have hh := (Subgroup.mem_normalizer_iff.mp htn u).mp hu
    simpa only [inv_inv] using hh
  have hct' : c = t*up := by
    rw [hct]
    dsimp only [up]
    group
  have ht' : W*t*W⁻¹ ∈ torusGroup A hs hp Base Index K :=
    (Subgroup.mem_normalizer_iff.mp
      (wordUnit_mem_torus_normalizer A hs hp Base Index K (expandRelative r)) t).mp ht
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

theorem exists_relative_inversion_cell (K : Type) [Field K] [Finite K]
    (sigma : K ≃+* K) (g : (Matrix GeckIndex GeckIndex K)ˣ)
    (hg : g ∈ CFSGTrialityGeckSourceWordAction.MatrixGroup K)
    (hfixed : unitTwist K sigma g = g) :
    ∃ (r : List Bool) (b : (Matrix GeckIndex GeckIndex K)ˣ),
      b ∈ normalizerEnvelope K ∧ ∃ v : InversionPart K (expandRelative r),
        g = b * wordUnit A hs hp Base Index K (expandRelative r) *
          inversionEmbedding K (expandRelative r) v := by
  obtain ⟨w,b,hb,c,hc,he,hinv⟩ := exists_fixed_bruhat_cell K sigma g hg hfixed
  exact exists_relative_inversion_cell_of_commuting_word K g b c w hb hc he
    (block_invariance_root_commutes w hinv)

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckRelativeBruhatCover
