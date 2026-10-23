import SymmetricSubgroupAsymptotics.CFSGTrialityGeckRootLineDiagonal
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckRelativeBruhatCover

/-! Relative Bruhat coordinates with a tracked all-root-line normalizing
diagonal factor. The stronger conclusion follows from the actual word
ratio and torus factors, rather than all simultaneous U/V normalizers. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckRootLineBruhatCover
open CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance
open CFSGTrialityRelativeWordLanguage CFSGTrialityGeckRootLineDiagonal
open CFSGTrialityD4InvariantRoots CFSGTrialityD4WordDiscriminant
open CFSGTrialityGeckNormalizerEnvelope CFSGTrialityGeckFixedBruhatCell
open CFSGTrialityGeckBruhatCellFactors CFSGTrialityGeckRelativeBruhatCover
open CFSGTrialityGeckMatrixTwist CFSGTrialityGeckPositiveTwist
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckIntegralWord
open CFSGNormTwoGeckBorelEnvelope CFSGNormTwoGeckBorelFactorization
open CFSGNormTwoGeckWeylWordTorus CFSGNormTwoCoordinateRootLineNormalizers
local notation "A" => CartanMatrix.D 4
local notation "hd" => CartanMatrix.D_diag 4
local notation "hs" => CartanMatrix.D_transpose 4
local notation "hp" => D4_positive_definite
local notation "ho" => CartanMatrix.D_off_diag_nonpos 4

theorem exists_rootLine_cell_of_commuting_word (K : Type) [Field K] [Finite K]
    (g b c : (Matrix GeckIndex GeckIndex K)ˣ) (w : List (Fin 4))
    (hb : b ∈ borelEnvelope A hs hp Base Index K)
    (hc : c ∈ borelEnvelope A hs hp Base Index K)
    (he : g = b * wordUnit A hs hp Base Index K w * c)
    (hcomm : ∀ k, diagramRoot (rootAction w k) = rootAction w (diagramRoot k)) :
    ∃ (r : List Bool) (u d : (Matrix GeckIndex GeckIndex K)ˣ),
      u ∈ Positive K ∧ d ∈ rootLineDiagonal K ∧
      ∃ v : InversionPart K (expandRelative r),
        g = (u*d) * wordUnit A hs hp Base Index K (expandRelative r) *
          inversionEmbedding K (expandRelative r) v := by
  obtain ⟨r,d,hdD,hword⟩ := CFSGTrialityGeckRootLineDiagonal.exists_relative_matrix_factor K w hcomm
  let W := wordUnit A hs hp Base Index K (expandRelative r)
  obtain ⟨u0,hu0,t0,ht0,hbt⟩ := borel_factor A hs hp Base Index K b hb
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
  let D := (t0*d)*(W*t*W⁻¹)
  have hD : D ∈ rootLineDiagonal K :=
    (rootLineDiagonal K).mul_mem
      ((rootLineDiagonal K).mul_mem (torus_le_rootLineDiagonal K ht0) hdD)
      (torus_le_rootLineDiagonal K ht')
  have hgn : g = (u0*D)*W*up := by
    rw [he,hword,hct',hbt]
    dsimp only [D,W]
    group
  obtain ⟨p,hpU,v,hprod⟩ := exists_positive_inversion_factors K (expandRelative r) ⟨up,hup⟩
  have hDP : D ∈ Subgroup.normalizer (Positive K : Set _) :=
    (rootLineDiagonal_le_diagonal K hD).1.1
  have hx : D*(W*p*W⁻¹)*D⁻¹ ∈ Positive K :=
    (Subgroup.mem_normalizer_iff.mp hDP (W*p*W⁻¹)).mp hpU
  refine ⟨r,u0*(D*(W*p*W⁻¹)*D⁻¹),D,(Positive K).mul_mem hu0 hx,hD,v,?_⟩
  calc
    g = (u0*D)*W*up := hgn
    _ = (u0*D)*W*(p*inversionEmbedding K (expandRelative r) v) :=
      congrArg (fun x => (u0*D)*W*x) hprod
    _ = _ := by
      dsimp only [W]
      group

theorem exists_rootLine_cell (K : Type) [Field K] [Finite K]
    (sigma : K ≃+* K) (g : (Matrix GeckIndex GeckIndex K)ˣ)
    (hg : g ∈ CFSGTrialityGeckSourceWordAction.MatrixGroup K)
    (hfixed : unitTwist K sigma g = g) :
    ∃ (r : List Bool) (u d : (Matrix GeckIndex GeckIndex K)ˣ),
      u ∈ Positive K ∧ d ∈ rootLineDiagonal K ∧
      ∃ v : InversionPart K (expandRelative r),
        g = (u*d) * wordUnit A hs hp Base Index K (expandRelative r) *
          inversionEmbedding K (expandRelative r) v := by
  obtain ⟨w,b,hb,c,hc,he,hinv⟩ := exists_fixed_bruhat_cell K sigma g hg hfixed
  exact exists_rootLine_cell_of_commuting_word K g b c w hb hc he
    (block_invariance_root_commutes w hinv)

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckRootLineBruhatCover
