import SymmetricSubgroupAsymptotics.EncodedPermutationConjugacyCover
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow25TopCertificate
import Mathlib.Tactic.FinCases

/-!
# Original-row conjugacy cover for selected sixteen-frame row 25

The selected witness uses the retained 768 original rows and historical
24 representative labels. Every conjugator is an index in those same rows.
The literal data were transcribed from the selected original-conjugacy
witness file; the pointwise equations below are the proof obligations.
No class-separation or centralizer-count theorem is used by this cover.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow25ConjugacyCover

abbrev Source := PrimitiveAffineSixteenFrameRow25TopCertificate.Source
local instance sourceGroup : Group Source :=
  PrimitiveAffineSixteenFrameRow25TopCertificate.group

private abbrev certificate := PrimitiveAffineSixteenFrameRow25TopCertificate.certificate

private def representativeTable : Array (Fin 768) :=
  #[0,5,285,37,389,96,116,245,576,537,507,17,182,38,317,625,453,355,578,517,289,459,76,34]

private def labelTable : Array (Fin 24) :=
  #[0,14,13,11,6,1,15,19,20,15,12,12,13,12,11,20,13,11,4,17,12,8,7,14,23,15,23,22,7,21,22,16,12,14,23,21,14,3,13,12,13,12,15,12,13,23,13,22,12,6,11,7,15,22,16,21,12,12,13,12,16,13,14,16,22,13,13,12,13,10,22,12,10,5,13,17,22,20,17,23,12,20,15,22,10,18,20,17,22,12,10,9,16,18,21,18,5,15,14,13,13,12,17,17,20,22,18,12,18,15,13,17,22,16,6,11,6,13,20,12,17,23,13,13,12,12,20,21,20,13,15,12,13,17,18,22,6,10,23,20,19,13,13,12,13,17,12,22,12,10,20,23,23,9,21,19,20,12,20,16,11,13,12,21,12,13,18,13,20,15,12,12,13,22,14,22,20,6,20,19,15,2,12,13,12,13,14,13,12,12,20,13,7,8,6,16,20,19,13,13,12,13,19,12,15,12,12,13,14,22,19,13,16,12,13,22,15,23,14,11,12,13,17,16,12,14,20,13,7,2,22,21,18,21,8,23,6,20,20,13,13,13,19,12,2,7,13,22,18,12,20,21,13,22,7,14,15,15,22,20,2,12,13,12,13,16,13,13,12,12,19,20,16,14,13,22,21,23,20,13,13,12,22,12,14,2,12,13,18,20,22,14,22,13,22,14,13,3,19,6,12,13,22,20,16,3,12,20,17,13,15,18,6,12,13,12,23,14,13,22,12,18,15,13,19,21,16,3,12,13,20,13,23,12,22,13,15,18,16,22,22,6,13,18,13,12,21,22,23,13,13,13,8,13,19,17,20,18,13,19,13,22,13,12,12,14,20,13,21,12,13,23,22,14,12,16,13,12,15,12,13,22,14,11,17,14,20,13,20,4,16,12,18,23,15,9,10,12,21,13,18,22,12,12,13,13,21,13,23,9,11,22,22,12,12,13,12,13,20,11,22,22,6,20,15,12,13,12,19,12,13,12,18,23,21,1,12,13,12,15,12,13,21,12,20,21,13,13,17,18,13,12,22,16,19,20,13,22,20,21,12,13,23,12,12,13,10,12,21,17,19,17,16,21,12,12,13,15,12,20,11,13,14,19,1,22,20,18,21,23,17,15,16,7,8,7,12,10,13,9,22,12,12,13,21,22,20,10,13,12,14,13,18,17,13,19,13,19,12,12,13,20,17,13,15,17,10,12,12,20,13,13,12,20,12,7,10,9,12,10,13,1,23,21,19,21,12,20,22,10,12,13,20,13,19,12,20,19,4,11,10,18,13,17,14,12,7,21,17,12,13,19,20,10,12,12,8,23,18,13,17,7,13,7,12,12,12,13,12,19,15,21,12,13,12,13,18,8,12,10,23,16,13,12,13,12,12,22,7,16,15,23,15,23,23,15,18,21,15,2,21,12,13,12,13,15,12,18,15,23,16,23,12,12,23,21,12,13,15,23,21,18,18,15,7,12,10,23,13,12,23,23,15,18,18,21,12,13,21,8,12,13,23,23,7,15,12,15,18,23,18,21,18,21,23,9,21,15,23,22,21,15,7,23,2,21,9,13,2,21,18,16,7,13,12,13,18,21,23,9,8,13,7,2,13,15,12,18,23,1,7,8,9,2,7,8,2,18,18,10,7,15,7,8,15,1,23,7,2,9,23,23,18,21,18,15,10,23,21,18,23,18,21,18,9,21,21,18,21,18,5,5,23,15,10,15,15,18,18,21,18,10,5,10,5,10,15,15]

private def conjugatorTable : Array (Fin 768) :=
  #[0,25,616,29,7,0,7,6,26,21,221,19,643,62,3,40,434,0,1,52,81,29,7,21,11,1,2,173,14,1,62,183,25,175,0,21,63,0,0,246,2,166,5,438,424,3,3,99,88,1,46,27,8,65,65,5,436,70,439,9,174,394,7,6,38,227,19,135,6,35,112,247,55,1,230,174,0,21,17,59,287,5,54,3,11,33,10,65,26,255,2,62,14,58,54,57,0,15,3,84,1,151,66,6,174,6,9,97,18,22,397,51,1,1,24,8,0,161,63,353,53,4,12,613,163,26,175,28,19,11,153,360,7,24,50,7,6,23,16,36,25,43,477,34,406,62,42,24,83,9,34,57,13,65,15,26,6,152,62,8,1,129,104,78,110,393,14,13,52,51,206,33,392,19,1,20,173,21,1,174,13,6,0,89,236,97,5,200,76,3,99,98,1,25,20,20,65,65,20,85,210,64,183,159,3,22,1,222,6,195,5,92,49,8,59,4,60,58,19,13,224,237,4,3,7,24,102,29,4,25,14,7,16,75,46,12,3,11,178,68,82,33,62,36,26,0,23,49,2,205,108,53,17,17,8,51,32,26,5,4,1,167,153,20,87,5,5,42,85,194,1,2,25,53,8,25,23,55,3,21,9,24,10,216,174,0,5,207,161,0,106,17,61,183,2,66,618,4,19,19,405,246,21,64,13,3,28,17,15,54,73,3,62,447,4,323,17,0,229,64,138,4,23,239,14,51,7,13,89,45,7,27,115,21,11,88,27,13,62,187,47,5,462,49,16,64,77,178,42,262,52,26,6,83,21,0,51,12,149,8,74,34,56,147,82,62,20,46,69,74,53,37,102,52,52,26,58,102,69,211,433,67,15,7,20,65,79,204,15,0,63,71,153,1,2,24,57,14,59,66,60,50,50,23,152,212,19,71,7,6,21,71,36,187,92,147,128,103,24,5,70,33,65,48,57,101,191,77,28,18,148,212,79,5,114,2,59,425,87,9,145,150,20,47,9,3,77,76,175,73,187,30,57,0,22,69,447,55,100,0,2,81,21,60,150,25,16,31,8,3,7,19,29,13,49,17,99,14,13,101,25,62,69,20,4,18,35,10,25,39,5,6,22,46,8,34,161,93,22,1,22,67,79,155,118,9,14,0,69,10,4,51,54,63,67,13,188,0,38,232,30,60,25,31,24,69,29,46,43,18,32,55,6,53,204,26,54,0,149,39,206,9,129,6,3,65,99,49,16,8,12,224,23,198,49,57,32,63,6,6,40,38,182,7,20,55,12,93,1,129,180,66,33,4,40,239,0,10,0,184,21,43,134,25,11,186,96,15,29,29,12,45,27,186,53,102,11,1,32,15,46,21,65,68,157,178,370,32,3,19,39,51,18,27,20,58,32,11,16,24,37,54,199,100,261,0,58,23,11,66,66,8,4,188,76,2,98,185,10,52,62,5,6,49,13,16,1,78,399,155,85,23,50,69,24,17,15,255,43,23,156,178,56,6,2,4,51,38,22,28,15,12,1,57,25,4,4,25,38,72,29,79,45,29,8,10,19,125,13,39,43,28,38,28,56,73,119,24,65,15,7,96,10,7,101,33,117,56,43,34,23,13,22,3,11,28,4,40,39,5,24,29,6,3,82,11,53,9,14,5,69,24,51,42,8,52,10,15,129,7,93,27,16,21,20,56,46,52,38,26,2,6,117,43,38,119,40,25,82,52,29,22,10,6,9,24,161,56]

def representativeRow (j : Fin 24) : Fin 768 := representativeTable[j.val]!
def labelRow (i : Fin 768) : Fin 24 := labelTable[i.val]!
def conjugatorRow (i : Fin 768) : Fin 768 := conjugatorTable[i.val]!

private def pointCheck (i : Fin 768) (x : Fin 16) : Prop :=
  finFunctionFinEquiv.symm (certificate.rows (conjugatorRow i))
      (finFunctionFinEquiv.symm (certificate.rows i) x) =
    finFunctionFinEquiv.symm (certificate.rows (representativeRow (labelRow i)))
      (finFunctionFinEquiv.symm (certificate.rows (conjugatorRow i)) x)

private instance pointCheck_decidable (i : Fin 768) (x : Fin 16) :
    Decidable (pointCheck i x) := by
  unfold pointCheck
  infer_instance

/-- Each declaration checks exactly 96 retained rows against all 16 points. -/
private theorem points_block0 : ∀ (i : Fin 96) (x : Fin 16),
    pointCheck (((i.castAdd 96).castAdd 192).castAdd 384) x := by
  refine Fin.addCases (m := 48) (n := 48) ?_ ?_ <;>
    refine Fin.addCases (m := 24) (n := 24) ?_ ?_ <;>
      refine Fin.addCases (m := 12) (n := 12) ?_ ?_ <;>
        decide +kernel

private theorem points_block1 : ∀ (i : Fin 96) (x : Fin 16),
    pointCheck (((i.natAdd 96).castAdd 192).castAdd 384) x := by
  refine Fin.addCases (m := 48) (n := 48) ?_ ?_ <;>
    refine Fin.addCases (m := 24) (n := 24) ?_ ?_ <;>
      refine Fin.addCases (m := 12) (n := 12) ?_ ?_ <;>
        decide +kernel

private theorem points_block2 : ∀ (i : Fin 96) (x : Fin 16),
    pointCheck (((i.castAdd 96).natAdd 192).castAdd 384) x := by
  refine Fin.addCases (m := 48) (n := 48) ?_ ?_ <;>
    refine Fin.addCases (m := 24) (n := 24) ?_ ?_ <;>
      refine Fin.addCases (m := 12) (n := 12) ?_ ?_ <;>
        decide +kernel

private theorem points_block3 : ∀ (i : Fin 96) (x : Fin 16),
    pointCheck (((i.natAdd 96).natAdd 192).castAdd 384) x := by
  refine Fin.addCases (m := 48) (n := 48) ?_ ?_ <;>
    refine Fin.addCases (m := 24) (n := 24) ?_ ?_ <;>
      refine Fin.addCases (m := 12) (n := 12) ?_ ?_ <;>
        decide +kernel

private theorem points_block4 : ∀ (i : Fin 96) (x : Fin 16),
    pointCheck (((i.castAdd 96).castAdd 192).natAdd 384) x := by
  refine Fin.addCases (m := 48) (n := 48) ?_ ?_ <;>
    refine Fin.addCases (m := 24) (n := 24) ?_ ?_ <;>
      refine Fin.addCases (m := 12) (n := 12) ?_ ?_ <;>
        decide +kernel

private theorem points_block5 : ∀ (i : Fin 96) (x : Fin 16),
    pointCheck (((i.natAdd 96).castAdd 192).natAdd 384) x := by
  refine Fin.addCases (m := 48) (n := 48) ?_ ?_ <;>
    refine Fin.addCases (m := 24) (n := 24) ?_ ?_ <;>
      refine Fin.addCases (m := 12) (n := 12) ?_ ?_ <;>
        decide +kernel

private theorem points_block6 : ∀ (i : Fin 96) (x : Fin 16),
    pointCheck (((i.castAdd 96).natAdd 192).natAdd 384) x := by
  refine Fin.addCases (m := 48) (n := 48) ?_ ?_ <;>
    refine Fin.addCases (m := 24) (n := 24) ?_ ?_ <;>
      refine Fin.addCases (m := 12) (n := 12) ?_ ?_ <;>
        decide +kernel

private theorem points_block7 : ∀ (i : Fin 96) (x : Fin 16),
    pointCheck (((i.natAdd 96).natAdd 192).natAdd 384) x := by
  refine Fin.addCases (m := 48) (n := 48) ?_ ?_ <;>
    refine Fin.addCases (m := 24) (n := 24) ?_ ?_ <;>
      refine Fin.addCases (m := 12) (n := 12) ?_ ?_ <;>
        decide +kernel

private theorem points_checked : ∀ (i : Fin 768) (x : Fin 16), pointCheck i x := by
  refine Fin.addCases (m := 384) (n := 384) ?_ ?_ <;>
    refine Fin.addCases (m := 192) (n := 192) ?_ ?_ <;>
      refine Fin.addCases (m := 96) (n := 96) ?_ ?_
  · exact points_block0
  · exact points_block1
  · exact points_block2
  · exact points_block3
  · exact points_block4
  · exact points_block5
  · exact points_block6
  · exact points_block7

/-- The selected conjugacy equation is checked in the faithful original
permutation image, using only the retained codes. -/
theorem conjugates_checked : ∀ (i : Fin 768) (x : Fin 16),
    finFunctionFinEquiv.symm (certificate.rows (conjugatorRow i))
        (finFunctionFinEquiv.symm (certificate.rows i) x) =
      finFunctionFinEquiv.symm (certificate.rows (representativeRow (labelRow i)))
        (finFunctionFinEquiv.symm (certificate.rows (conjugatorRow i)) x) :=
  points_checked

/-- Conjugacy coverage is inside the original row group; the faithful
permutation action is used only to verify its equations. -/
def cover : FiniteConjugacyCover
    (fun i : Fin 768 => (⟨i⟩ : Source)) 24 :=
  certificate.rowConjugacyCoverOfPoints
    PrimitiveAffineSixteenFrameRow25TopCertificate.rows_injective
    PrimitiveAffineSixteenFrameRow25TopCertificate.previousRow
    PrimitiveAffineSixteenFrameRow25TopCertificate.previous_checked
    representativeRow labelRow conjugatorRow conjugates_checked

/-- The cover uses precisely the representatives in the retained normal
transition certificates. -/
theorem representative_eq (j : Fin 24) :
    (⟨cover.representative j⟩ : Source) =
      PrimitiveAffineSixteenFrameRow25TopCertificate.representative j := by
  change (⟨representativeRow j⟩ : Source) =
    PrimitiveAffineSixteenFrameRow25TopCertificate.representative j
  fin_cases j <;> rfl

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow25ConjugacyCover

end
