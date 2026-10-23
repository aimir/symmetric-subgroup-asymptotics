import SymmetricSubgroupAsymptotics.CFSGTrialityGeckBorelTwist
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckBruhatBlockUniqueness
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckIntegralWord
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateBruhatCover
import Mathlib.Tactic.Group

/-! A fixed element of the actual Geck group lies in a triality-stable
Weyl block cell. Only the checked ambient cover, Borel stability and
actual block uniqueness are used; no fixed-factor exactness is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedBruhatCell
open CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance
open CFSGTrialityGeckMatrixTwist CFSGTrialityGeckBorelTwist
open CFSGTrialityGeckRootSubgroupTwist CFSGTrialityGeckWeylBlocks
open CFSGTrialityGeckBruhatBlockUniqueness CFSGNormTwoGeckIntegralWord
open CFSGNormTwoGeckBorelEnvelope CFSGNormTwoGeckWeylWordDegree
open CFSGSerreQuadraticMatrix CFSGSerreDiagram
open CFSGNormTwoRootPairing CFSGNormTwoCartanDiagramRoots CFSGNormTwoCartanDiagramWords

theorem block_invariance_root_commutes (w : List (Fin 4))
    (hinv : wordBlockPermutation (w.map trialityPermutation) = wordBlockPermutation w)
    (k : Roots (CartanMatrix.D 4)) :
    rootPermutation (CartanMatrix.D 4) trialityPermutation triality_preserves
      (wordRoot (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
        D4_positive_definite Base Index w k) =
    wordRoot (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
      D4_positive_definite Base Index w
      (rootPermutation (CartanMatrix.D 4) trialityPermutation triality_preserves k) := by
  have h := congrArg (fun p => p
    (some (rootPermutation (CartanMatrix.D 4) trialityPermutation triality_preserves k))) hinv
  change some (rootWordPermutation (w.map trialityPermutation)
      (rootPermutation (CartanMatrix.D 4) trialityPermutation triality_preserves k)) =
    some (rootWordPermutation w
      (rootPermutation (CartanMatrix.D 4) trialityPermutation triality_preserves k)) at h
  have hr := Option.some.inj h
  rw [rootWordPermutation_apply, rootWordPermutation_apply] at hr
  exact (wordRoot_permutation (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
    (CartanMatrix.D_transpose 4) D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4)
    trialityPermutation triality_preserves w k).trans hr

theorem unitTwist_wordUnit (K : Type) [Field K] (sigma : K ≃+* K)
    (w : List (Fin 4)) :
    unitTwist K sigma (wordUnit (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
      D4_positive_definite Base Index K w) =
      wordUnit (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
        D4_positive_definite Base Index K (w.map trialityPermutation) := by
  simpa only [word_eq_canonicalWord] using unitTwist_word K sigma w

private theorem fixed_cell_rearrange {G : Type*} [Group G]
    (tau : G →* G) (g b c w w' : G)
    (hf : tau g = g) (he : g = b * w * c) (hw : tau w = w') :
    (b⁻¹ * tau b) * w' * (tau c * c⁻¹) = w := by
  calc
    _ = b⁻¹ * tau g * c⁻¹ := by rw [he, map_mul, map_mul, hw]; group
    _ = w := by rw [hf, he]; group

theorem fixed_bruhat_cell_block (K : Type) [Field K] (sigma : K ≃+* K)
    (g b c : (Matrix GeckIndex GeckIndex K)ˣ) (w : List (Fin 4))
    (hfixed : unitTwist K sigma g = g)
    (hb : b ∈ borelEnvelope (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
      D4_positive_definite Base Index K)
    (hc : c ∈ borelEnvelope (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
      D4_positive_definite Base Index K)
    (he : g = b * wordUnit (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
      D4_positive_definite Base Index K w * c) :
    wordBlockPermutation (w.map trialityPermutation) = wordBlockPermutation w := by
  let B := borelEnvelope (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
    D4_positive_definite Base Index K
  apply actual_bruhat_block_unique K (w.map trialityPermutation) w
    (b⁻¹ * unitTwist K sigma b) (unitTwist K sigma c * c⁻¹)
  · exact B.mul_mem (B.inv_mem hb) (unitTwist_borel_mem K sigma b hb)
  · exact B.mul_mem (unitTwist_borel_mem K sigma c hc) (B.inv_mem hc)
  · exact fixed_cell_rearrange (unitTwist K sigma).toMonoidHom g b c _ _
      hfixed he (unitTwist_wordUnit K sigma w)

theorem exists_fixed_bruhat_cell (K : Type) [Field K] (sigma : K ≃+* K)
    (g : (Matrix GeckIndex GeckIndex K)ˣ)
    (hg : g ∈ canonicalElementaryGroup rawData K)
    (hfixed : unitTwist K sigma g = g) :
    ∃ (w : List (Fin 4)) (b : (Matrix GeckIndex GeckIndex K)ˣ),
      b ∈ borelEnvelope (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
        D4_positive_definite Base Index K ∧
      ∃ c : (Matrix GeckIndex GeckIndex K)ˣ,
        c ∈ borelEnvelope (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
          D4_positive_definite Base Index K ∧
        g = b * wordUnit (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
          D4_positive_definite Base Index K w * c ∧
        wordBlockPermutation (w.map trialityPermutation) = wordBlockPermutation w := by
  obtain ⟨w, b, hb, c, hc, he⟩ := CFSGNormTwoCoordinateBruhatCover.canonical_bruhat_cover
    (CartanMatrix.D 4) (CartanMatrix.D_diag 4) (CartanMatrix.D_transpose 4)
    D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4) K g hg
  exact ⟨w, b, hb, c, hc, he, fixed_bruhat_cell_block K sigma g b c w hfixed hb hc he⟩

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedBruhatCell
