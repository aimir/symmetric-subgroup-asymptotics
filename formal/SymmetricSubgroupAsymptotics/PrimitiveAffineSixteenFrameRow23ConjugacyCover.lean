import SymmetricSubgroupAsymptotics.EncodedPermutationConjugacyCover
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow23TopCertificate
import Mathlib.Tactic.FinCases

/-!
# Original-row conjugacy cover for selected sixteen-frame row 23

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

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow23ConjugacyCover

abbrev Source := PrimitiveAffineSixteenFrameRow23TopCertificate.Source
local instance sourceGroup : Group Source :=
  PrimitiveAffineSixteenFrameRow23TopCertificate.group

private abbrev certificate := PrimitiveAffineSixteenFrameRow23TopCertificate.certificate

private def representativeTable : Array (Fin 768) :=
  #[0,552,379,645,16,314,266,1,228,332,706,115,67,641,630,763,58,346,431,104,705,487,749,318]

private def labelTable : Array (Fin 24) :=
  #[0,7,6,4,4,12,8,7,10,19,8,6,6,6,18,6,4,17,10,6,16,18,16,6,8,11,8,21,11,19,11,22,21,22,8,11,11,21,8,6,6,18,6,6,18,8,6,18,18,18,11,6,6,6,18,6,16,18,16,8,22,11,6,6,6,18,18,12,21,18,18,18,6,22,18,4,1,6,6,18,6,11,11,21,8,11,22,6,11,21,20,19,6,11,8,11,22,22,6,8,8,11,22,22,19,18,21,22,21,8,22,10,1,7,8,11,20,11,22,8,22,21,22,7,11,8,21,4,6,18,11,4,18,12,18,8,4,6,18,6,18,18,18,11,21,11,4,6,18,18,18,20,12,18,18,6,19,18,6,8,8,8,22,11,6,18,6,18,11,6,18,18,18,8,6,6,6,18,17,22,18,18,6,18,6,11,11,8,19,19,11,8,8,22,8,6,18,6,11,18,22,18,18,6,18,2,22,22,8,21,18,18,6,18,18,6,21,18,6,6,6,19,10,22,18,18,18,6,8,6,3,5,14,3,18,3,14,18,6,6,10,8,6,7,22,20,10,11,11,22,20,22,5,6,8,22,23,19,18,20,23,23,9,23,8,3,6,18,6,8,8,21,6,8,22,23,22,21,11,3,6,6,18,6,11,21,6,20,19,7,18,18,22,22,22,11,22,9,8,18,21,19,22,11,3,3,14,6,10,7,20,10,11,20,5,10,23,20,23,3,7,11,8,23,3,10,8,20,19,14,21,22,9,21,6,10,10,20,7,10,19,10,4,16,4,18,17,10,22,16,18,18,16,16,1,16,10,8,10,2,16,4,16,11,4,18,20,17,18,6,18,5,10,11,8,23,7,8,22,2,17,23,16,18,6,18,23,20,9,16,17,1,16,18,6,23,16,6,1,6,23,16,18,6,3,10,20,11,8,10,18,16,18,18,18,18,18,23,16,6,11,11,19,8,18,6,19,18,5,6,6,18,11,22,6,19,3,23,22,10,16,20,6,18,6,19,18,6,23,20,16,16,6,6,23,6,6,9,6,6,18,6,18,23,19,19,22,6,8,11,20,7,6,6,18,6,3,11,6,18,16,11,6,3,8,6,1,21,17,17,7,18,9,6,20,20,22,9,18,23,23,9,23,11,6,3,1,6,9,18,23,20,10,20,18,18,6,20,23,8,23,20,10,18,20,10,7,10,18,23,10,8,6,5,23,20,18,20,11,6,18,9,17,22,9,6,20,19,17,9,16,17,1,6,6,20,20,10,9,23,6,9,23,23,20,18,23,20,7,23,5,17,6,7,3,10,20,1,5,6,9,23,23,6,6,18,23,6,23,21,23,6,11,10,20,6,11,23,23,18,6,8,7,23,20,18,12,18,18,6,18,23,18,6,18,14,6,23,9,18,12,3,23,3,16,1,20,6,20,23,14,3,20,6,20,3,23,5,6,5,3,13,5,20,20,3,23,6,18,10,18,11,20,6,23,18,3,7,6,18,6,20,18,7,9,18,23,10,18,6,10,7,20,18,10,18,10,18,9,18,7,10,7,18,18,6,6,10,18,20,18,6,7,6,6,8,10,6,18,20,13,10,18,9,23,20,10,18,8,18,20,10,18,9,10,18,7,9,10,19,9,10,10,18,10,18,6,18,13,3,21,3,5,22,21,13,19,22,9,19,6,22,22,22,15,22,10,15,1,22,15,21,7,15,1,15,10,15,15,15,10,22,15,15,15,19,15,9]

private def conjugatorTable : Array (Fin 768) :=
  #[0,0,7,48,1,4,10,4,117,121,2,178,6,59,122,24,0,11,116,111,8,85,1,3,6,77,46,10,23,4,106,112,11,115,1,25,32,2,23,155,21,43,67,30,27,19,56,91,139,271,6,204,1,88,86,99,4,25,0,62,34,72,5,101,18,111,35,0,14,140,6,45,29,116,33,9,10,23,98,142,189,43,19,27,25,99,24,184,2,45,14,45,77,13,35,98,81,35,146,30,50,78,39,50,0,64,6,10,46,37,77,112,2,11,246,0,121,16,14,8,49,1,96,2,36,99,24,10,181,12,40,6,22,12,63,77,14,58,13,20,37,42,18,3,13,10,5,180,53,74,7,37,35,66,21,64,13,70,26,233,12,27,44,45,57,2,186,89,30,183,118,46,8,52,66,208,82,1,40,12,14,26,83,9,281,15,48,36,35,127,4,15,13,86,88,202,87,17,44,71,15,167,36,255,28,6,2,19,14,23,44,75,131,47,10,27,47,16,104,40,89,46,34,25,49,29,60,33,0,50,39,1,7,10,65,23,10,4,51,91,231,49,68,127,6,7,76,21,12,84,25,40,2,31,85,30,21,10,207,3,43,12,14,2,42,11,0,150,102,28,79,35,48,26,82,13,42,39,11,24,154,87,146,9,27,44,4,30,11,121,19,120,54,27,61,39,91,2,84,58,12,37,92,42,26,15,3,15,98,39,78,23,20,246,0,10,5,36,0,2,46,17,18,16,6,35,121,8,2,2,4,76,0,8,159,86,49,15,13,54,43,232,32,112,2,5,0,44,23,25,15,248,113,12,36,6,91,92,228,1,115,37,44,35,11,20,77,2,39,13,137,3,50,56,7,17,12,78,90,0,3,62,37,40,53,51,36,99,11,48,12,15,10,62,19,35,23,176,3,63,10,24,57,105,28,92,233,5,265,27,17,308,11,96,52,128,222,11,141,8,28,14,12,43,3,46,44,73,8,72,16,0,24,11,78,36,12,4,228,14,2,88,76,54,167,38,31,244,56,28,152,34,47,60,3,164,179,10,65,174,268,172,94,20,14,47,28,49,117,60,236,38,168,160,130,107,36,1,35,82,14,8,108,42,16,10,42,0,23,6,10,134,4,14,79,18,232,8,135,60,52,47,19,7,61,37,35,42,1,223,1,85,30,6,200,116,198,4,31,159,9,49,15,68,136,6,114,19,109,7,25,136,110,9,15,26,83,16,18,11,216,44,17,233,13,114,2,39,5,12,11,1,0,166,52,84,27,77,39,48,12,24,46,24,1,132,87,42,36,82,16,7,55,37,25,48,46,13,4,2,46,69,84,109,34,97,14,145,6,34,28,298,31,96,13,193,9,25,18,84,37,4,43,32,117,107,2,88,108,119,24,29,143,36,110,1,143,26,6,81,10,1,61,13,35,12,265,135,52,8,0,16,23,43,19,4,65,11,165,6,7,0,25,12,92,0,78,117,103,84,80,29,35,38,30,32,18,45,137,239,54,62,179,14,45,138,77,42,219,140,82,35,10,203,11,72,39,105,35,133,34,28,47,125,165,32,116,2,38,43,221,162,44,294,90,236,12,45,124,50,15,81,129,23,23,0,0,297,3,112,159,4,163,27,16,299,143,115,3,34,143,1,24,41,8,34,144,93,3,8,76,3,26,1,143,4,115,18,76,143,106,8,4,16,2,3,18,16,4,0,4,115,115,6,16,26,7,1,11,3,40,7,13,0,8,114,23,34]

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
    PrimitiveAffineSixteenFrameRow23TopCertificate.rows_injective
    PrimitiveAffineSixteenFrameRow23TopCertificate.previousRow
    PrimitiveAffineSixteenFrameRow23TopCertificate.previous_checked
    representativeRow labelRow conjugatorRow conjugates_checked

/-- The cover uses precisely the representatives in the retained normal
transition certificates. -/
theorem representative_eq (j : Fin 24) :
    (⟨cover.representative j⟩ : Source) =
      PrimitiveAffineSixteenFrameRow23TopCertificate.representative j := by
  change (⟨representativeRow j⟩ : Source) =
    PrimitiveAffineSixteenFrameRow23TopCertificate.representative j
  fin_cases j <;> rfl

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow23ConjugacyCover

end
