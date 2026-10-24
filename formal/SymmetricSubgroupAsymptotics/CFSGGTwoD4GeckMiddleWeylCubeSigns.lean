import SymmetricSubgroupAsymptotics.CFSGTrialityGeckShortComplement
import SymmetricSubgroupAsymptotics.CFSGTrialityD4CubeComplement
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleCubeEdges

/-! The actual short Weyl word exchanges complementary middle cube roots.
The corresponding original root words have primitive integral parameter
signs. These are root-word identities, not an identification of an
abstract rank-one group or its quotient action. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleWeylCubeSigns
open CFSGTrialityD4NormTwo CFSGTrialityD4MiddleCube CFSGTrialityD4CubeComplement
open CFSGTrialityD4RelativeComplementRoots CFSGTrialityGeckShortComplement
open CFSGTrialityGeckDiagramCovariance CFSGTrialityGeckFixedRootWords
open CFSGTrialityGeckMiddleCubeEdges CFSGNormTwoCoordinateLatticeWord
open CFSGNormTwoGeckWeylWordDegree
open CFSGNormTwoCoordinateWordRootElementSign CFSGNormTwoCoordinateSelectedRootElement
local notation "A" => CartanMatrix.D 4
local notation "hd" => CartanMatrix.D_diag 4
local notation "hs" => CartanMatrix.D_transpose 4
local notation "hp" => D4_positive_definite
local notation "ho" => CartanMatrix.D_off_diag_nonpos 4
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots A) := Classical.decEq _

theorem short_word_cube_complement (a : Cube) :
    wordRoot A hs hp Base Index [0,2,3] (cubeRoot a) = cubeRoot (complement a) := by
  apply Subtype.ext
  rw [short_word_root_coordinates]
  have h : ∀ b : Cube, shortStep *ᵥ (cubeRoot b).val = (cubeRoot (complement b)).val := by
    decide +kernel
  exact h a

theorem shortWeyl_cube_sign (a : Cube) :
    ∃ e : ℤ, (e=1 ∨ e= -1) ∧ ∀ (K : Type) [Field K] (t : K),
      shortWeyl K*cubeWord K a t*(shortWeyl K)⁻¹ =
        cubeWord K (complement a) ((e : K)*t) := by
  obtain ⟨e,he,hw⟩ := word_selected_root_sign A hd hs hp ho [0,2,3] (cubeRoot a)
  refine ⟨e,he,?_⟩
  intro K _ t
  have h := hw K t
  change shortWeyl K*cubeWord K a t*(shortWeyl K)⁻¹ =
    selectedRootElement A hd hs hp ho K
      (wordRoot A hs hp Base Index [0,2,3] (cubeRoot a)) ((e : K)*t) at h
  rw [short_word_cube_complement] at h
  exact h

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleWeylCubeSigns
