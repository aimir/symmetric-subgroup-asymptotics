import SymmetricSubgroupAsymptotics.EncodedPermutationConjugacyCover
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow26TopCertificate
import Mathlib.Tactic.FinCases

/-!
# Original-row conjugacy cover for selected sixteen-frame row 26

The selected witness uses the retained 768 original rows and historical
19 representative labels. Every conjugator is an index in those same rows.
The literal data were transcribed from the selected original-conjugacy
witness file; the pointwise equations below are the proof obligations.
No class-separation or centralizer-count theorem is used by this cover.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow26ConjugacyCover

abbrev Source := PrimitiveAffineSixteenFrameRow26TopCertificate.Source
local instance sourceGroup : Group Source :=
  PrimitiveAffineSixteenFrameRow26TopCertificate.group

private abbrev certificate := PrimitiveAffineSixteenFrameRow26TopCertificate.certificate

private def representativeTable : Array (Fin 768) :=
  #[0,5,185,38,765,698,601,724,511,762,651,416,294,609,502,717,274,567,191]

private def labelTable : Array (Fin 19) :=
  #[0,11,10,6,6,1,13,14,17,13,9,10,10,14,10,8,17,10,8,1,11,9,6,8,11,16,12,15,17,8,17,15,12,9,11,15,17,11,3,10,10,16,10,9,12,10,10,9,16,15,15,10,9,10,17,9,8,8,8,12,17,12,17,10,9,9,15,10,8,12,9,8,6,11,15,10,9,9,9,6,15,9,6,2,10,11,16,18,9,11,16,9,17,18,12,9,13,17,6,11,17,13,15,10,8,8,9,14,12,17,6,11,12,2,14,12,18,11,10,9,9,11,11,17,11,10,11,14,10,11,15,14,6,6,9,18,10,10,16,12,9,10,16,9,9,18,17,6,10,18,10,10,12,10,9,9,16,11,18,8,12,15,12,9,11,11,15,6,10,13,9,10,17,10,9,6,16,15,9,9,10,17,5,13,9,2,6,15,9,6,2,18,16,12,17,13,17,12,18,9,14,14,6,9,10,12,9,17,9,10,18,12,11,10,10,12,10,5,13,14,10,9,12,6,18,9,6,15,11,6,18,17,13,13,2,9,9,15,9,10,11,9,10,10,9,15,10,6,7,6,14,15,18,9,10,10,17,7,13,10,7,7,13,9,10,10,11,15,13,9,12,12,10,16,16,10,17,11,6,10,16,9,15,16,12,18,13,16,6,9,10,15,12,9,12,15,9,8,15,17,14,6,13,7,16,18,6,18,17,13,10,10,9,2,1,18,10,9,15,16,12,10,13,10,1,9,17,15,7,18,12,8,11,15,7,18,7,18,16,13,18,2,9,9,9,10,17,14,6,18,16,15,16,18,10,10,11,18,9,18,16,17,11,8,2,9,15,12,8,2,9,11,16,11,10,16,15,16,6,9,13,12,9,9,11,9,9,10,15,16,11,11,14,16,7,6,11,9,12,15,8,16,10,9,9,18,10,13,9,9,10,11,9,16,14,10,11,11,17,10,6,1,18,13,15,12,15,16,10,9,16,9,13,17,8,16,15,9,10,12,9,11,7,17,9,10,9,7,13,14,16,12,15,8,9,9,14,10,14,9,7,13,16,7,18,7,11,13,10,9,13,10,7,10,13,10,9,11,16,13,9,12,2,13,10,16,6,11,18,9,10,10,18,9,16,15,9,16,10,15,10,11,14,6,9,13,10,9,12,9,17,8,10,15,10,10,12,7,17,18,10,15,16,18,18,10,10,13,10,17,9,6,10,12,18,13,12,13,16,9,12,13,8,9,14,10,9,15,10,16,18,7,10,11,10,9,18,9,15,17,10,9,10,7,17,10,5,17,15,14,12,12,8,10,18,9,17,9,10,7,16,7,17,10,9,17,9,17,14,6,9,10,14,12,8,14,10,15,17,14,10,6,3,6,10,16,14,8,9,13,11,10,10,18,16,12,6,10,14,18,12,9,10,10,10,15,14,15,9,10,13,9,18,12,13,17,10,10,9,7,14,9,18,6,17,13,10,13,14,18,6,10,7,6,10,14,18,10,9,9,10,9,11,14,16,13,13,13,13,14,18,10,13,17,9,6,9,17,9,17,6,7,14,14,14,9,18,11,3,5,9,9,14,9,10,6,14,16,5,2,17,9,15,9,13,14,10,10,10,13,5,14,6,14,13,18,3,15,16,2,12,9,9,10,7,18,14,10,9,16,1,10,14,10,6,15,11,9,13,12,12,14,11,10,14,10,10,14,9,16,10,6,6,17,9,9,11,14,9,6,4,4,9,14,18,4,6,14]

private def conjugatorTable : Array (Fin 768) :=
  #[0,157,31,48,2,0,31,121,26,35,168,85,166,118,108,5,6,232,22,35,48,80,51,2,23,14,34,33,73,9,43,42,134,157,26,41,57,11,0,38,55,18,64,94,38,113,107,86,16,63,56,148,48,197,27,284,8,10,12,64,96,39,15,242,26,37,96,90,30,96,35,26,85,49,128,11,85,24,121,50,6,36,24,3,41,27,189,4,234,15,13,84,175,67,43,289,2,11,43,1,88,45,10,245,13,6,125,29,7,31,52,21,97,7,16,6,26,41,72,34,116,7,121,106,79,115,5,86,42,22,11,34,6,14,431,16,47,134,51,15,137,88,22,120,262,59,9,98,53,23,3,390,57,56,207,60,58,2,76,14,1,88,25,266,75,3,2,25,29,9,141,96,19,223,108,86,1,25,174,126,252,40,6,30,7,0,5,37,69,139,15,0,7,11,34,63,33,27,6,32,38,21,53,220,39,3,9,89,57,145,65,40,24,14,89,108,101,2,108,35,151,20,10,38,30,130,22,119,34,9,60,176,51,11,6,38,331,15,175,37,38,113,198,102,30,45,116,11,6,33,8,48,18,29,224,44,48,45,48,16,25,54,23,253,30,24,97,27,29,115,5,23,40,23,0,77,3,85,28,57,97,103,105,17,4,8,21,21,39,81,2,38,17,65,0,30,156,19,5,28,13,41,59,10,12,42,89,11,42,27,83,6,28,4,2,17,84,102,39,5,33,144,1,97,9,15,29,49,30,2,26,25,57,32,27,194,19,32,6,26,89,1,155,254,114,157,54,33,10,12,66,130,4,58,132,152,90,22,10,62,71,13,43,18,8,55,9,12,7,25,71,20,10,25,60,26,23,31,118,42,10,24,150,11,139,178,61,86,34,25,96,6,4,59,8,94,13,75,45,12,27,19,259,160,5,29,139,15,46,270,266,73,51,29,17,43,0,61,30,130,35,11,61,13,81,90,31,73,8,250,3,118,8,20,4,88,29,4,79,62,72,132,7,117,3,48,87,91,38,31,2,85,17,3,104,1,22,50,20,99,26,42,44,1,39,12,33,25,61,117,40,26,17,258,36,10,63,56,11,55,43,65,14,39,209,27,7,60,106,47,138,196,3,70,36,13,76,20,23,3,73,39,0,26,21,5,19,198,9,54,32,0,81,132,22,32,42,28,70,108,99,36,40,128,79,92,45,147,387,10,8,21,141,79,70,6,28,148,45,23,22,12,1,17,117,155,78,4,206,135,24,24,142,9,269,49,19,259,1,25,292,96,7,5,37,69,9,0,7,11,140,8,46,54,105,127,8,101,20,15,30,4,23,167,237,56,90,4,2,34,22,164,45,132,45,44,51,19,2,14,87,0,3,42,4,39,30,95,13,0,16,65,70,207,64,13,1,5,24,10,30,40,80,13,25,108,23,8,154,165,14,166,21,2,16,1,63,98,135,2,5,97,47,40,5,7,15,54,3,135,56,0,57,13,46,7,88,137,83,356,27,33,28,12,8,20,3,56,46,75,40,71,22,39,27,49,56,82,25,7,160,3,48,26,9,31,37,192,14,1,14,12,36,151,74,27,40,35,0,27,101,89,71,53,4,87,261,238,204,17,10,46,20,1,57,25,4,0,9,26,107,224,95,28,0,1,42,21,6,37,4,76,51,59,15,47,59,19,89,41,49,27,10,17,10,147,1,63,73,32,12,73,75,35,16,258,4,73,2,3,6,1,0,59,5,0,173,6]

def representativeRow (j : Fin 19) : Fin 768 := representativeTable[j.val]!
def labelRow (i : Fin 768) : Fin 19 := labelTable[i.val]!
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
    (fun i : Fin 768 => (⟨i⟩ : Source)) 19 :=
  certificate.rowConjugacyCoverOfPoints
    PrimitiveAffineSixteenFrameRow26TopCertificate.rows_injective
    PrimitiveAffineSixteenFrameRow26TopCertificate.previousRow
    PrimitiveAffineSixteenFrameRow26TopCertificate.previous_checked
    representativeRow labelRow conjugatorRow conjugates_checked

/-- The cover uses precisely the representatives in the retained normal
transition certificates. -/
theorem representative_eq (j : Fin 19) :
    (⟨cover.representative j⟩ : Source) =
      PrimitiveAffineSixteenFrameRow26TopCertificate.representative j := by
  change (⟨representativeRow j⟩ : Source) =
    PrimitiveAffineSixteenFrameRow26TopCertificate.representative j
  fin_cases j <;> rfl

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow26ConjugacyCover

end
