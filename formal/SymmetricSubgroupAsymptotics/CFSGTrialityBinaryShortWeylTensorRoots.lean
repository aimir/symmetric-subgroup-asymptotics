import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleFirstLayer
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateWordRootElementSign
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckNonnegativeHeightFlag
import Mathlib.Algebra.CharP.Two

/-! The literal outer-three Weyl word flips the actual middle-root cube
and preserves its middle grading. Parameter signs are first integral
units and are removed only in characteristic two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityBinaryShortWeylTensorRoots
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGTrialityD4NormTwo
open CFSGTrialityD4MiddleCube CFSGTrialityGeckDiagramCovariance
open CFSGTrialityGeckMiddleFirstLayer CFSGNormTwoGeckWeylWordDegree
open CFSGNormTwoCoordinateWordRootElementSign CFSGNormTwoCoordinateSelectedRootElement
open CFSGSerreQuadraticWeylWord CFSGGradedMatrixSubgroups
local notation "A" => CartanMatrix.D 4
local notation "hd" => CartanMatrix.D_diag 4
local notation "hs" => CartanMatrix.D_transpose 4
local notation "hp" => D4_positive_definite
local notation "ho" => CartanMatrix.D_off_diag_nonpos 4
local instance trialityShortWeylRootsDecidableEq : DecidableEq (Roots A) := Classical.decEq _

private abbrev U (K : Type) [CommRing K] := (Matrix GeckIndex GeckIndex K)ˣ
private abbrev parameter (K : Type) [Field K] (a : Cube) (t : K) : U K :=
  selectedRootElement A hd hs hp ho K (cubeRoot a) t
private abbrev W (K : Type) [Field K] : U K := canonicalWord rawData K [0,2,3]

def flip (a : Cube) : Cube := fun i => (a i).rev

private def latticeWord : List (Fin 4) → (Fin 4 → ℤ) → (Fin 4 → ℤ)
  | [],v => v
  | i::w,v => latticeWord w v-
      integerPairing A (latticeWord w v) (Pi.single i (1 : ℤ)) • Pi.single i (1 : ℤ)
private theorem wordRoot_val (w : List (Fin 4)) (k : Roots A) :
    (wordRoot A hs hp Base Index w k).val=latticeWord w k.val := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change (wordRoot A hs hp Base Index w k).val-
      integerPairing A (wordRoot A hs hp Base Index w k).val (Pi.single i (1 : ℤ)) •
        Pi.single i (1 : ℤ)=latticeWord (i::w) k.val
    rw [ih]
    rfl

theorem short_word_root (a : Cube) :
    wordRoot A hs hp Base Index [0,2,3] (cubeRoot a)=cubeRoot (flip a) := by
  apply Subtype.ext
  rw [wordRoot_val]
  change latticeWord [0,2,3] (cubeCoordinates a)=cubeCoordinates (flip a)
  revert a
  decide

theorem short_word_preserving (K : Type) [Field K] :
    canonicalWord rawData K [0,2,3] ∈ preservingUnits middleWeight := by
  have hz : ∀ i ∈ ([0,2,3] : List (Fin 4)), middleFunctional (Index i : Roots A).val=0 := by
    intro i hi
    simp at hi
    rcases hi with rfl | rfl | rfl <;> rfl
  have h := CFSGNormTwoGeckNonnegativeHeightFlag.zero_degree_word_preserving
    A hs hp Base Index middleFunctional K [0,2,3] hz
  have hw : CFSGNormTwoGeckHeightSupport.weight A hs hp Base middleFunctional=middleWeight := by
    funext i
    exact CFSGNormTwoGeckLatticeDegree.weight_proj A hs hp Base (1 : Fin 4) i
  simpa only [hw] using h

theorem short_word_conjugate_parameter (K : Type) [Field K] [CharP K 2]
    (a : Cube) (t : K) :
    W K * parameter K a t * (W K)⁻¹ = parameter K (flip a) t := by
  obtain ⟨ε,hε,he⟩ := word_selected_root_sign A hd hs hp ho [0,2,3] (cubeRoot a)
  have hsign : (ε : K)=1 := by
    rcases hε with rfl | rfl <;> simp only [Int.cast_one,Int.cast_neg,CharTwo.neg_eq]
  have h := he K t
  have hroot : wordRoot A hs hp (coordinateBase A hd hs hp ho)
      (coordinateIndexEquiv A hd hs hp ho) [0,2,3] (cubeRoot a) =
        cubeRoot (flip a) := short_word_root a
  rw [hroot,hsign,one_mul] at h
  exact h

end SymmetricSubgroupAsymptotics.CFSGTrialityBinaryShortWeylTensorRoots
