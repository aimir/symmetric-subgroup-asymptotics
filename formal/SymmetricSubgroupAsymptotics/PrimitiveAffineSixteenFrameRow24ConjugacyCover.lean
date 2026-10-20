import SymmetricSubgroupAsymptotics.EncodedPermutationConjugacyCover
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow24TopCertificate
import Mathlib.Tactic.FinCases

/-!
# Original-row conjugacy cover for selected sixteen-frame row 24

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

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow24ConjugacyCover

abbrev Source := PrimitiveAffineSixteenFrameRow24TopCertificate.Source
local instance sourceGroup : Group Source :=
  PrimitiveAffineSixteenFrameRow24TopCertificate.group

private abbrev certificate := PrimitiveAffineSixteenFrameRow24TopCertificate.certificate

private def representativeTable : Array (Fin 768) :=
  #[0,108,412,14,555,635,396,297,245,270,419,1,32,285,741,141,334,375,336]

private def labelTable : Array (Fin 19) :=
  #[0,11,9,6,6,12,11,17,12,9,10,9,11,10,3,8,17,9,8,3,9,12,18,13,6,15,11,15,6,15,17,13,12,15,15,12,9,10,18,9,10,9,13,10,10,10,18,15,9,10,10,10,8,15,9,8,8,13,15,13,15,10,9,10,17,10,8,8,13,8,6,1,9,10,9,15,15,10,13,11,18,9,18,16,13,9,10,18,12,17,11,14,17,12,10,6,7,9,12,13,15,8,11,15,12,3,13,16,1,11,13,18,9,18,11,14,10,12,11,11,11,18,12,15,6,10,10,15,6,9,10,15,13,6,9,10,10,18,10,9,9,15,17,15,18,6,9,9,16,9,10,10,13,9,10,15,11,16,13,11,11,18,10,9,12,9,9,9,17,9,9,9,10,10,6,15,12,14,10,10,10,17,6,5,12,1,6,10,15,18,13,6,17,15,12,7,15,12,16,18,14,11,12,10,13,9,10,9,15,9,10,10,16,11,9,9,9,1,12,10,5,6,12,16,9,6,16,6,9,8,6,15,7,10,15,7,9,9,10,9,17,11,10,11,14,8,9,16,17,13,14,16,14,16,6,9,9,16,13,13,10,18,11,18,10,16,12,10,9,9,9,10,13,16,13,10,17,11,18,15,14,8,17,13,8,13,18,13,9,9,9,15,10,8,1,10,3,7,7,10,10,10,17,9,12,18,12,10,13,17,9,10,16,17,14,12,8,16,12,16,7,7,18,18,7,7,9,17,11,16,16,11,7,11,16,14,18,16,18,9,10,7,17,9,16,18,16,18,18,9,16,16,10,11,18,9,17,16,13,17,10,9,8,10,10,17,13,11,9,2,14,8,9,9,11,17,16,12,16,2,17,6,10,9,10,9,9,9,13,16,9,10,14,10,9,10,6,17,15,13,9,14,9,17,14,14,11,14,18,16,6,13,2,9,10,13,9,9,14,10,9,9,18,9,10,17,10,10,12,9,14,9,17,14,9,18,9,16,16,16,6,17,10,9,10,15,7,9,9,9,9,15,6,7,6,17,13,12,18,16,18,18,9,15,9,10,10,10,10,7,13,10,7,12,9,7,18,7,6,10,9,11,9,15,14,9,18,12,10,13,13,17,14,13,18,1,7,12,17,3,14,7,11,10,14,18,18,17,9,12,9,12,10,10,10,14,6,10,9,17,9,14,14,16,18,16,16,10,17,10,9,9,14,9,13,18,16,10,12,6,18,7,17,16,11,10,6,18,11,9,6,11,10,10,9,4,10,6,6,12,9,9,11,10,12,10,10,6,18,9,10,11,9,15,18,16,10,10,6,14,9,11,17,17,16,17,12,13,9,11,10,8,17,9,15,6,10,6,11,14,15,15,6,12,12,10,14,11,10,10,16,13,18,15,10,10,13,14,13,5,12,6,18,15,15,18,9,13,10,10,9,9,8,6,10,5,10,11,9,9,16,12,10,10,17,10,10,10,9,13,9,13,15,14,1,6,10,14,5,14,7,1,16,14,10,12,13,14,11,12,6,10,10,7,9,15,16,14,9,12,13,15,11,9,14,17,9,17,10,9,14,10,11,9,17,6,16,8,10,8,16,17,4,1,17,12,9,10,10,9,9,10,8,17,15,9,11,11,1,15,6,12,6,10,11,10,12,1,14,8,17,12,16,18,12,13,4,10,13,15,7,14,14,11,3,1,5,14,6,14,8,6,11,9,15,14,10,14,9,9,10,15,14,6,6,14,10,4]

private def conjugatorTable : Array (Fin 768) :=
  #[0,0,6,37,113,20,145,30,5,3,5,241,70,21,0,19,31,75,4,8,24,2,77,42,46,37,3,31,95,39,28,3,0,74,10,8,28,66,22,94,12,123,11,15,212,25,73,54,66,26,278,6,58,105,118,11,20,38,7,16,22,54,100,16,7,306,32,37,6,9,10,1,18,97,12,51,11,20,54,47,98,147,13,9,37,16,72,5,38,21,37,81,53,247,98,7,39,146,29,8,78,16,178,30,16,2,7,30,0,9,15,3,64,1,13,29,29,7,54,41,2,21,98,61,24,13,270,9,122,61,3,4,61,44,70,48,32,140,36,102,99,0,17,29,47,33,116,126,25,4,23,82,13,5,57,17,42,21,4,139,224,20,14,63,10,206,30,208,57,65,114,7,259,53,15,15,1,23,124,175,208,15,55,5,131,3,114,301,2,159,9,28,8,55,197,36,60,6,15,55,80,10,43,163,2,179,188,68,90,36,333,35,87,206,17,199,76,4,4,121,2,75,133,3,21,21,55,38,46,22,11,21,42,108,38,46,54,56,79,32,12,112,30,133,57,0,287,14,10,25,33,83,42,8,1,2,125,95,40,23,133,46,36,97,86,36,60,51,23,33,0,128,5,2,20,205,48,33,2,20,47,42,95,69,5,0,28,10,153,119,137,28,280,18,13,22,33,0,4,37,81,115,13,307,62,39,78,4,36,39,190,220,40,33,9,185,23,118,59,1,9,7,134,12,35,12,85,76,39,38,47,56,11,43,0,186,0,50,85,74,84,22,115,91,19,80,89,74,10,93,44,49,130,11,9,108,45,135,76,3,1,180,12,288,28,11,72,113,121,5,39,1,352,221,147,0,20,47,4,1,37,5,94,289,271,364,186,157,17,98,105,67,11,34,104,123,0,43,6,1,8,40,82,4,13,22,202,34,118,69,72,21,0,124,214,81,40,15,107,0,128,110,29,301,189,54,71,114,17,120,41,11,2,76,112,26,1,24,41,11,12,16,385,134,64,1,26,10,156,53,207,53,30,20,53,71,107,113,56,7,49,8,187,5,45,118,38,41,102,5,106,76,10,3,34,2,7,1,2,52,280,17,43,25,78,41,76,61,232,57,73,42,20,124,24,6,8,33,97,10,37,6,15,127,56,41,33,47,67,146,27,23,18,8,100,25,39,139,135,22,286,10,21,42,14,10,43,65,46,2,57,346,35,320,31,15,54,31,56,9,95,19,36,12,19,228,48,30,4,132,20,35,344,249,109,0,91,171,35,15,319,269,8,40,207,10,83,6,102,178,132,379,202,3,54,23,89,106,82,19,29,411,51,35,13,9,11,189,139,160,60,14,60,37,97,3,63,13,141,31,23,13,36,22,99,140,54,134,187,137,29,116,34,47,99,384,33,36,131,9,73,40,53,79,8,50,98,35,7,104,113,117,84,51,33,0,135,62,243,19,138,86,116,9,20,19,113,290,60,112,62,39,43,5,15,8,62,60,8,70,3,5,5,15,27,139,121,8,146,25,81,279,131,15,384,36,28,1,344,41,70,24,61,9,38,18,279,1,69,39,17,39,381,334,29,14,34,8,229,3,39,50,13,25,5,39,133,224,68,138,31,17,7,14,14,306,116,124,23,33,23,34,84,61,185,112,200,7,113,2,23,13,6,6,80,34,4,80,19,130,14,0,16,34,4,22,1,3,25,4,57,115,69,189,26,7,235,59,222,35,73,102,2,26,22,6,243,3]

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
    PrimitiveAffineSixteenFrameRow24TopCertificate.rows_injective
    PrimitiveAffineSixteenFrameRow24TopCertificate.previousRow
    PrimitiveAffineSixteenFrameRow24TopCertificate.previous_checked
    representativeRow labelRow conjugatorRow conjugates_checked

/-- The cover uses precisely the representatives in the retained normal
transition certificates. -/
theorem representative_eq (j : Fin 19) :
    (⟨cover.representative j⟩ : Source) =
      PrimitiveAffineSixteenFrameRow24TopCertificate.representative j := by
  change (⟨representativeRow j⟩ : Source) =
    PrimitiveAffineSixteenFrameRow24TopCertificate.representative j
  fin_cases j <;> rfl

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow24ConjugacyCover

end
