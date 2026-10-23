import SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedRootSections
import SymmetricSubgroupAsymptotics.CFSGTrialityD4RelativeRootWords
import SymmetricSubgroupAsymptotics.CFSGTrialityD4PositiveRootIndex
import SymmetricSubgroupAsymptotics.CFSGTrialityFixedWeylWords

/-! Exact original lattice labels and heights of the fixed sections.
The top short layer has the explicit cyclic reindexing forced by its
actual relative reflection word. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckSectionRootLabels
open CFSGNormTwoRootPairing CFSGTrialityD4NormTwo CFSGSerreQuadraticWeylWord
open CFSGTrialityGeckDiagramCovariance CFSGTrialityGeckFixedRootWords
open CFSGTrialityGeckFixedRootSections CFSGTrialityD4PositiveRootOrbits
open CFSGTrialityD4PositiveRootIndex CFSGIntegerHeightSign

def shortWord : Fin 3 → List (Fin 4) := ![[], [1], [0,2,3,1]]
def longWord : Fin 3 → List (Fin 4) := ![[], [0,2,3], [1,0,2,3]]

def shortLabel (s k : Fin 3) : Roots (CartanMatrix.D 4) :=
  ![shortRoot 0 k, shortRoot 1 k, shortRoot 2 (cycle k)] s

theorem short_seed_index (k : Fin 3) :
    shortRoot 0 k = (Index (CFSGTrialityFixedWeylWords.outerNode k) : Roots (CartanMatrix.D 4)) := by
  apply Subtype.ext
  funext j
  change shortCoordinates 0 k j =
    (Pi.single (CFSGTrialityFixedWeylWords.outerNode k) (1 : ℤ) : Fin 4 → ℤ) j
  fin_cases k <;> fin_cases j <;> decide

theorem long_seed_index : longRoot 0 = (Index 1 : Roots (CartanMatrix.D 4)) := by
  apply Subtype.ext
  funext j
  change longCoordinates 0 j = (Pi.single (1 : Fin 4) (1 : ℤ) : Fin 4 → ℤ) j
  fin_cases j <;> decide

theorem shortTransport_word (K : Type) [CommRing K] (s : Fin 3) :
    shortTransport K s = canonicalWord rawData K (shortWord s) := by
  fin_cases s
  · rfl
  · rfl
  · change canonicalWord rawData K [0,2,3] * canonicalWord rawData K [1] =
      canonicalWord rawData K [0,2,3,1]
    simp only [canonicalWord, mul_one, mul_assoc]

theorem longTransport_word (K : Type) [CommRing K] (s : Fin 3) :
    longTransport K s = canonicalWord rawData K (longWord s) := by
  fin_cases s
  · rfl
  · rfl
  · change canonicalWord rawData K [1] * canonicalWord rawData K [0,2,3] =
      canonicalWord rawData K [1,0,2,3]
    simp only [canonicalWord, mul_one, mul_assoc]

theorem short_word_label (s k : Fin 3) :
    CFSGTrialityD4RelativeRootWords.rootWord (shortWord s) (shortRoot 0 k) = shortLabel s k := by
  fin_cases s
  · rfl
  · exact CFSGTrialityD4RelativeRootWords.short_middle k
  · exact CFSGTrialityD4RelativeRootWords.short_top k

theorem long_word_label (s : Fin 3) :
    CFSGTrialityD4RelativeRootWords.rootWord (longWord s) (longRoot 0) = longRoot s := by
  fin_cases s
  · rfl
  · exact CFSGTrialityD4RelativeRootWords.long_middle
  · exact CFSGTrialityD4RelativeRootWords.long_top

theorem short_label_height (s k : Fin 3) : height (shortLabel s k).val = ![(1 : ℤ),2,3] s := by
  fin_cases s
  · exact short_height 0 k
  · exact short_height 1 k
  · exact short_height 2 (cycle k)

theorem short_label_positive (s k : Fin 3) (j : Fin 4) : 0 ≤ (shortLabel s k).val j := by
  fin_cases s
  · exact short_positive 0 k j
  · exact short_positive 1 k j
  · exact short_positive 2 (cycle k) j

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckSectionRootLabels
