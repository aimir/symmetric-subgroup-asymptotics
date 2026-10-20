import SymmetricSubgroupAsymptotics.EncodedPermutationConjugacyCover
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow27TopCertificate
import Mathlib.Tactic.FinCases

/-!
# Original-row conjugacy cover for selected sixteen-frame row 27

The selected witness uses the retained 1536 original rows and historical
33 representative labels. Every conjugator is an index in those same rows.
The literal data were transcribed from the selected original-conjugacy
witness file; the pointwise equations below are the proof obligations.
No class-separation or centralizer-count theorem is used by this cover.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow27ConjugacyCover

abbrev Source := PrimitiveAffineSixteenFrameRow27TopCertificate.Source
local instance sourceGroup : Group Source :=
  PrimitiveAffineSixteenFrameRow27TopCertificate.group

private abbrev certificate := PrimitiveAffineSixteenFrameRow27TopCertificate.certificate

private def representativeTable : Array (Fin 1536) :=
  #[0,228,816,538,827,664,1085,1,121,993,863,1011,1218,629,1534,1141,1494,117,487,433,24,1075,1000,1074,144,1338,414,621,583,39,1252,510,1110]

private def labelTable : Array (Fin 33) :=
  #[0,7,27,4,4,28,7,10,28,6,27,27,27,4,10,27,8,31,28,31,8,31,31,8,20,6,6,6,27,28,31,6,27,27,28,12,27,27,6,29,11,11,8,31,27,27,11,31,12,29,8,11,11,29,11,8,29,6,24,24,24,6,11,8,24,6,6,11,8,28,28,11,24,6,6,6,27,31,27,11,28,8,26,16,17,16,26,6,6,20,8,29,32,32,8,6,6,32,11,11,17,16,27,6,29,8,8,27,26,16,16,26,8,32,29,32,11,17,16,29,26,8,32,32,29,8,29,32,8,26,6,6,6,24,32,32,6,24,32,32,11,8,32,6,24,20,24,6,11,17,32,8,16,32,32,8,11,29,6,20,6,8,11,24,6,6,6,32,8,8,28,8,11,29,18,26,26,26,16,11,11,26,29,1,26,26,26,18,24,24,6,28,11,8,11,32,24,24,8,32,26,26,6,6,24,11,32,29,29,8,6,11,26,12,8,26,26,6,6,24,11,29,11,6,18,26,26,26,1,26,26,28,11,11,8,32,26,26,11,29,32,26,26,12,26,11,29,18,26,26,1,28,8,11,11,29,26,26,11,28,11,8,11,28,11,11,26,26,26,6,8,11,26,6,8,11,32,29,8,26,6,6,26,8,29,26,11,8,32,29,11,26,6,24,29,29,6,20,26,8,29,32,26,26,32,26,8,29,29,32,11,11,6,6,29,29,8,11,32,6,24,6,8,26,6,6,24,8,32,11,6,7,31,28,31,7,32,32,19,18,18,18,26,29,32,18,26,26,28,31,8,29,18,26,7,32,29,8,27,3,3,5,26,32,29,3,27,18,18,18,19,6,6,31,31,30,11,6,6,31,8,18,18,24,20,6,31,8,11,32,3,26,32,5,18,24,24,6,28,8,29,20,24,11,29,32,18,26,26,31,32,26,32,3,26,26,26,18,6,11,8,26,7,19,18,18,18,28,18,27,5,3,3,19,7,30,31,31,8,31,11,3,5,26,26,28,8,8,11,29,26,18,26,31,18,3,26,18,31,8,26,19,18,18,18,27,3,5,7,31,30,31,11,3,5,28,11,18,18,26,3,31,8,7,31,31,28,18,31,7,28,31,31,4,26,30,4,26,31,30,8,8,4,26,26,18,31,8,18,30,31,11,31,4,26,8,11,26,3,31,8,11,18,5,8,31,11,8,11,31,26,26,8,11,29,32,11,26,3,26,26,18,31,11,29,26,18,5,18,26,26,3,31,8,32,26,26,31,28,8,26,32,26,11,11,8,29,3,26,24,20,6,26,18,28,10,10,7,10,29,9,10,10,28,18,22,23,25,23,18,10,7,29,29,22,18,18,26,32,10,28,9,10,32,25,18,29,29,10,10,9,29,8,11,6,27,27,27,5,11,11,27,3,10,10,29,11,27,1,13,27,27,27,27,6,25,23,22,10,26,10,31,23,25,6,6,9,28,31,27,18,11,27,23,6,26,10,30,6,6,30,8,27,1,5,7,11,3,27,18,18,18,22,30,18,18,6,31,10,29,29,8,23,18,26,32,10,9,10,29,32,8,27,1,29,32,27,25,6,29,29,10,9,18,25,22,23,18,10,7,22,18,10,10,25,18,29,6,27,27,27,3,10,27,22,25,10,7,10,31,23,25,9,31,23,10,30,30,10,27,1,7,27,22,10,30,31,8,10,23,18,18,9,18,27,3,1,27,25,28,28,1,29,23,25,22,10,25,27,27,27,6,10,10,9,31,10,30,27,27,3,1,10,30,31,23,18,10,22,27,3,27,7,28,1,28,9,10,10,30,27,10,23,7,28,28,10,9,10,23,7,27,4,10,31,30,2,4,23,10,30,25,10,9,27,2,31,4,27,10,30,28,25,27,31,10,31,30,9,4,2,28,31,30,4,27,1,3,27,10,28,5,25,27,27,10,30,9,30,18,31,30,31,10,27,3,23,5,10,25,18,27,23,18,18,18,27,31,30,18,18,26,9,10,18,31,10,32,11,23,27,18,18,8,28,31,31,18,18,31,18,30,7,27,7,32,29,32,29,30,31,18,18,18,31,31,18,31,18,19,22,32,9,32,28,18,21,25,18,31,9,7,18,10,32,9,31,22,21,7,19,29,32,32,18,32,32,29,32,7,6,6,6,6,29,32,11,8,6,27,29,9,18,32,29,8,6,27,8,26,15,15,15,15,15,27,26,6,6,6,31,6,30,26,26,9,7,31,6,21,30,6,31,9,26,10,15,27,27,6,22,21,7,19,22,26,10,32,8,6,27,11,32,32,15,27,6,26,25,26,29,31,18,28,9,32,29,7,7,10,32,27,9,9,15,6,7,32,32,29,8,18,18,18,18,22,32,32,9,18,21,10,31,32,10,18,21,7,32,32,6,6,6,27,29,32,6,27,29,29,6,27,30,7,23,21,31,9,10,22,7,19,22,10,32,6,27,32,32,27,9,25,9,29,9,10,18,22,18,7,32,32,6,27,15,21,29,32,22,32,32,31,32,18,21,29,6,6,7,6,6,10,6,28,7,10,29,27,32,6,31,9,9,29,18,21,22,32,23,27,27,15,6,10,9,27,31,30,31,10,28,10,6,31,9,18,15,31,9,31,31,28,10,6,31,18,31,9,27,27,18,27,6,28,9,18,6,10,27,27,27,6,15,28,10,18,6,6,30,7,31,19,7,32,27,6,27,32,19,6,7,7,31,10,32,29,18,32,6,29,18,25,31,31,32,10,29,6,12,27,27,27,18,11,8,11,8,27,27,18,11,30,27,11,30,18,27,27,10,10,7,27,27,10,27,10,29,27,30,27,18,18,30,30,18,27,7,29,27,18,31,18,27,18,8,31,18,27,27,9,29,28,23,22,25,22,27,25,29,27,10,7,10,9,10,6,27,29,27,10,6,23,29,32,22,29,32,29,7,6,6,29,26,26,26,26,26,13,26,13,26,26,26,6,9,26,8,26,6,30,31,10,26,6,11,10,31,30,30,26,10,26,6,28,6,27,10,32,25,29,13,26,27,11,27,10,23,32,26,26,7,10,10,10,11,11,8,11,8,27,18,18,7,29,10,11,27,18,27,9,29,11,18,18,29,11,11,8,29,29,23,6,32,6,29,11,31,11,30,30,30,31,11,29,22,8,10,8,10,6,26,10,29,8,29,29,10,6,6,6,6,6,10,6,29,32,32,10,26,6,31,26,30,11,30,31,10,26,8,28,27,26,26,31,30,30,31,28,26,30,25,9,31,30,11,9,11,11,17,16,16,16,18,18,18,18,18,8,17,27,16,18,8,17,27,18,11,8,27,17,16,16,27,7,9,27,17,16,27,27,27,17,27,16,16,18,16,9,19,16,21,16,9,7,16,21,9,18,26,18,26,26,26,26,26,17,16,18,9,8,8,11,7,16,9,8,8,16,8,8,11,8,8,11,17,18,14,18,18,12,14,18,14,14,14,14]

private def conjugatorTable : Array (Fin 1536) :=
  #[0,0,303,86,38,8,4,101,2,103,429,228,285,16,85,153,38,191,27,224,39,108,90,16,0,86,38,88,460,11,220,110,244,456,21,8,240,246,46,0,132,23,217,190,124,139,161,371,2,16,134,58,133,5,75,79,1,71,9,2,13,96,9,105,11,201,149,24,92,10,28,74,25,217,200,210,237,192,119,55,22,24,46,15,1,16,3,51,42,1,9,97,48,84,166,16,94,35,62,155,2,36,115,116,93,87,223,304,19,5,87,31,2,78,42,15,59,0,38,40,6,0,114,87,18,8,60,52,23,45,122,55,156,4,20,67,155,10,49,95,26,41,68,23,0,4,15,109,73,3,36,91,17,45,153,40,25,64,53,3,87,106,27,3,95,48,99,85,103,88,15,59,92,38,3,23,55,148,40,39,127,105,15,2,133,184,24,6,18,14,31,5,46,73,79,118,8,7,25,109,4,144,209,50,29,41,100,104,4,95,67,56,99,21,133,54,59,105,40,19,105,3,54,98,31,258,34,47,0,9,108,1,34,19,11,86,61,66,43,105,44,380,80,10,73,47,41,12,122,124,8,173,52,14,84,47,195,56,83,82,78,21,37,35,103,87,347,397,44,148,155,166,100,81,77,44,50,6,54,178,62,161,14,13,19,97,6,29,51,7,95,346,138,26,72,14,54,12,147,32,46,37,205,25,107,53,67,17,80,103,45,90,139,123,43,34,46,31,116,63,12,108,42,89,41,52,6,75,83,71,20,2,128,36,129,20,34,80,1,15,36,44,106,88,5,38,94,40,42,265,58,87,13,62,49,106,107,1,3,19,11,13,145,40,44,10,6,5,1,16,2,164,66,57,130,17,40,61,100,131,27,42,40,21,6,73,113,31,106,105,17,146,41,3,18,1,17,9,18,74,13,14,5,42,207,17,24,41,16,264,19,161,79,18,0,200,13,17,75,16,26,58,8,8,147,75,73,17,25,31,18,6,4,0,111,7,24,60,10,51,80,7,15,88,65,582,33,76,17,106,87,9,194,158,165,14,74,7,59,28,26,5,33,201,11,12,25,12,57,25,339,69,118,16,7,336,7,2,86,91,21,73,68,24,54,10,175,0,32,9,84,228,13,183,78,36,357,84,3,84,55,161,15,177,15,96,12,70,87,175,0,38,229,35,37,71,193,35,26,31,151,1,186,6,4,2,86,22,36,431,85,83,30,15,145,121,88,36,0,95,27,56,72,5,79,38,66,19,76,1,92,9,9,3,38,138,7,23,97,62,123,88,39,35,107,143,78,2,64,16,7,27,86,68,20,215,49,10,153,8,67,3,13,0,30,23,127,41,56,4,14,51,217,223,18,202,144,98,18,108,37,10,7,47,22,37,95,20,12,10,150,9,100,52,12,4,24,15,4,4,67,0,12,19,17,45,121,64,12,0,14,40,1,5,6,9,2,3,68,18,51,49,130,129,35,65,4,43,114,17,98,18,18,57,147,90,20,5,26,74,18,7,144,11,0,150,3,5,16,14,43,97,83,38,41,142,25,153,1,103,150,69,7,64,42,43,176,51,32,36,16,85,13,10,102,46,7,15,83,37,23,259,29,153,17,91,53,48,111,21,6,164,48,230,125,65,2,3,75,48,74,3,6,27,9,2,30,291,69,20,59,57,291,52,24,8,1,582,4,66,13,67,9,37,45,338,68,12,191,16,321,27,21,74,25,13,4,56,11,7,591,3,35,23,6,21,21,56,57,32,10,19,54,23,143,21,71,336,186,2,22,21,38,174,30,5,185,36,40,11,15,142,143,344,22,111,64,370,231,192,87,433,1,64,177,49,112,27,270,8,27,522,39,113,111,15,0,90,122,128,35,90,190,7,111,1,112,0,36,263,82,205,8,44,155,233,4,39,11,5,5,83,231,40,1,33,27,8,97,166,397,1,1,76,38,435,90,25,16,58,71,92,230,0,73,1,4,5,267,5,26,164,54,32,132,10,86,8,173,28,131,142,59,224,143,430,2,42,68,10,30,141,20,15,64,338,1,162,151,7,54,51,28,68,23,75,69,31,77,4,48,77,299,70,56,35,29,104,258,7,5,27,35,9,432,8,1,16,23,483,2,11,322,82,25,20,101,55,7,50,9,51,14,1,286,72,30,25,29,112,33,76,44,292,75,22,13,6,15,58,67,49,182,60,73,14,228,202,101,30,5,1,4,10,18,98,12,97,56,113,335,207,21,179,43,1,432,6,92,2,59,14,174,0,5,81,3,43,42,7,0,10,442,10,35,81,35,77,213,2,96,0,7,53,8,41,39,171,86,17,21,84,148,51,5,74,116,113,115,34,69,37,82,113,9,142,231,12,32,155,5,49,114,240,124,1,10,2,15,300,8,229,259,11,173,150,21,22,108,62,144,82,145,147,32,71,59,165,29,33,111,321,10,229,0,0,82,111,78,26,237,4,15,15,55,0,26,26,23,118,173,38,229,55,8,129,119,39,118,29,76,54,89,65,2,4,117,3,8,4,0,125,157,67,17,54,77,34,130,47,18,87,205,4,132,103,156,132,28,5,39,90,130,85,52,5,16,93,17,143,28,0,299,155,57,185,46,232,15,490,290,338,36,16,39,21,19,40,24,103,19,143,174,24,5,315,17,9,230,120,251,247,163,113,16,304,4,265,298,442,236,11,6,229,423,69,10,13,113,26,14,21,25,33,131,8,201,13,17,32,59,58,34,170,73,10,53,161,64,84,57,39,79,166,6,5,27,49,0,128,182,29,303,53,44,29,107,258,286,50,8,20,21,21,24,140,162,141,187,125,55,20,67,131,63,158,22,315,231,150,252,271,0,432,128,148,54,30,23,22,92,121,121,317,36,433,63,70,54,54,70,442,9,2,3,10,49,24,68,69,25,232,9,290,31,132,299,74,8,16,37,15,151,64,87,52,21,31,290,143,28,26,67,29,116,239,290,12,240,4,33,2,273,150,55,57,78,117,91,9,336,57,32,126,69,90,173,8,25,69,192,48,115,50,1,77,79,8,0,50,3,10,151,77,251,220,25,145,52,76,437,89,60,72,76,32,18,11,47,52,301,246,436,71,56,2,322,115,53,436,161,10,139,123,62,104,93,60,11,76,36,177,82,146,28,145,215,60,23,11,2,175,157,12,38,64,92,17,104,58,21,73,83,93,100,101,24,17,43,290,194,21,39,29,213,104,97,46,20,22,45,11,229,28,111,78,40,143,34,237,114,8,292,36,112,130,87,115,51,49,35,232,38,57,30,437,97,33,5,1,35,39,111,456,236,429,228,45,9,22,84,247,102,86,271,298,22,37,252,16,2,54,140,62,23,317,38,8,123,301,300,24,50,23,7,244,4,38,25,9,25,92,174,238,0,9,112,285,50,522,115,22,132,109,28,125,10,120,231,80,19,12,445,21,338,43,72,25,145,104,64,97,207,72,56,460,8,237,442,4,2,230,1,6,0,3]

def representativeRow (j : Fin 33) : Fin 1536 := representativeTable[j.val]!
def labelRow (i : Fin 1536) : Fin 33 := labelTable[i.val]!
def conjugatorRow (i : Fin 1536) : Fin 1536 := conjugatorTable[i.val]!

private def pointCheck (i : Fin 1536) (x : Fin 16) : Prop :=
  finFunctionFinEquiv.symm (certificate.rows (conjugatorRow i))
      (finFunctionFinEquiv.symm (certificate.rows i) x) =
    finFunctionFinEquiv.symm (certificate.rows (representativeRow (labelRow i)))
      (finFunctionFinEquiv.symm (certificate.rows (conjugatorRow i)) x)

private instance pointCheck_decidable (i : Fin 1536) (x : Fin 16) :
    Decidable (pointCheck i x) := by
  unfold pointCheck
  infer_instance

/-- Each declaration checks 96 retained rows, on the original points. -/
private theorem points_block0 : ∀ (i : Fin 96) (x : Fin 16),
    pointCheck ((((i.castAdd 96).castAdd 192).castAdd 384).castAdd 768) x := by
  refine Fin.addCases (m := 48) (n := 48) ?_ ?_ <;>
    refine Fin.addCases (m := 24) (n := 24) ?_ ?_ <;>
      refine Fin.addCases (m := 12) (n := 12) ?_ ?_ <;>
        decide +kernel

private theorem points_block1 : ∀ (i : Fin 96) (x : Fin 16),
    pointCheck ((((i.natAdd 96).castAdd 192).castAdd 384).castAdd 768) x := by
  refine Fin.addCases (m := 48) (n := 48) ?_ ?_ <;>
    refine Fin.addCases (m := 24) (n := 24) ?_ ?_ <;>
      refine Fin.addCases (m := 12) (n := 12) ?_ ?_ <;>
        decide +kernel

private theorem points_block2 : ∀ (i : Fin 96) (x : Fin 16),
    pointCheck ((((i.castAdd 96).natAdd 192).castAdd 384).castAdd 768) x := by
  refine Fin.addCases (m := 48) (n := 48) ?_ ?_ <;>
    refine Fin.addCases (m := 24) (n := 24) ?_ ?_ <;>
      refine Fin.addCases (m := 12) (n := 12) ?_ ?_ <;>
        decide +kernel

private theorem points_block3 : ∀ (i : Fin 96) (x : Fin 16),
    pointCheck ((((i.natAdd 96).natAdd 192).castAdd 384).castAdd 768) x := by
  refine Fin.addCases (m := 48) (n := 48) ?_ ?_ <;>
    refine Fin.addCases (m := 24) (n := 24) ?_ ?_ <;>
      refine Fin.addCases (m := 12) (n := 12) ?_ ?_ <;>
        decide +kernel

private theorem points_block4 : ∀ (i : Fin 96) (x : Fin 16),
    pointCheck ((((i.castAdd 96).castAdd 192).natAdd 384).castAdd 768) x := by
  refine Fin.addCases (m := 48) (n := 48) ?_ ?_ <;>
    refine Fin.addCases (m := 24) (n := 24) ?_ ?_ <;>
      refine Fin.addCases (m := 12) (n := 12) ?_ ?_ <;>
        decide +kernel

private theorem points_block5 : ∀ (i : Fin 96) (x : Fin 16),
    pointCheck ((((i.natAdd 96).castAdd 192).natAdd 384).castAdd 768) x := by
  refine Fin.addCases (m := 48) (n := 48) ?_ ?_ <;>
    refine Fin.addCases (m := 24) (n := 24) ?_ ?_ <;>
      refine Fin.addCases (m := 12) (n := 12) ?_ ?_ <;>
        decide +kernel

private theorem points_block6 : ∀ (i : Fin 96) (x : Fin 16),
    pointCheck ((((i.castAdd 96).natAdd 192).natAdd 384).castAdd 768) x := by
  refine Fin.addCases (m := 48) (n := 48) ?_ ?_ <;>
    refine Fin.addCases (m := 24) (n := 24) ?_ ?_ <;>
      refine Fin.addCases (m := 12) (n := 12) ?_ ?_ <;>
        decide +kernel

private theorem points_block7 : ∀ (i : Fin 96) (x : Fin 16),
    pointCheck ((((i.natAdd 96).natAdd 192).natAdd 384).castAdd 768) x := by
  refine Fin.addCases (m := 48) (n := 48) ?_ ?_ <;>
    refine Fin.addCases (m := 24) (n := 24) ?_ ?_ <;>
      refine Fin.addCases (m := 12) (n := 12) ?_ ?_ <;>
        decide +kernel

private theorem points_block8 : ∀ (i : Fin 96) (x : Fin 16),
    pointCheck ((((i.castAdd 96).castAdd 192).castAdd 384).natAdd 768) x := by
  refine Fin.addCases (m := 48) (n := 48) ?_ ?_ <;>
    refine Fin.addCases (m := 24) (n := 24) ?_ ?_ <;>
      refine Fin.addCases (m := 12) (n := 12) ?_ ?_ <;>
        decide +kernel

private theorem points_block9 : ∀ (i : Fin 96) (x : Fin 16),
    pointCheck ((((i.natAdd 96).castAdd 192).castAdd 384).natAdd 768) x := by
  refine Fin.addCases (m := 48) (n := 48) ?_ ?_ <;>
    refine Fin.addCases (m := 24) (n := 24) ?_ ?_ <;>
      refine Fin.addCases (m := 12) (n := 12) ?_ ?_ <;>
        decide +kernel

private theorem points_block10 : ∀ (i : Fin 96) (x : Fin 16),
    pointCheck ((((i.castAdd 96).natAdd 192).castAdd 384).natAdd 768) x := by
  refine Fin.addCases (m := 48) (n := 48) ?_ ?_ <;>
    refine Fin.addCases (m := 24) (n := 24) ?_ ?_ <;>
      refine Fin.addCases (m := 12) (n := 12) ?_ ?_ <;>
        decide +kernel

private theorem points_block11 : ∀ (i : Fin 96) (x : Fin 16),
    pointCheck ((((i.natAdd 96).natAdd 192).castAdd 384).natAdd 768) x := by
  refine Fin.addCases (m := 48) (n := 48) ?_ ?_ <;>
    refine Fin.addCases (m := 24) (n := 24) ?_ ?_ <;>
      refine Fin.addCases (m := 12) (n := 12) ?_ ?_ <;>
        decide +kernel

private theorem points_block12 : ∀ (i : Fin 96) (x : Fin 16),
    pointCheck ((((i.castAdd 96).castAdd 192).natAdd 384).natAdd 768) x := by
  refine Fin.addCases (m := 48) (n := 48) ?_ ?_ <;>
    refine Fin.addCases (m := 24) (n := 24) ?_ ?_ <;>
      refine Fin.addCases (m := 12) (n := 12) ?_ ?_ <;>
        decide +kernel

private theorem points_block13 : ∀ (i : Fin 96) (x : Fin 16),
    pointCheck ((((i.natAdd 96).castAdd 192).natAdd 384).natAdd 768) x := by
  refine Fin.addCases (m := 48) (n := 48) ?_ ?_ <;>
    refine Fin.addCases (m := 24) (n := 24) ?_ ?_ <;>
      refine Fin.addCases (m := 12) (n := 12) ?_ ?_ <;>
        decide +kernel

private theorem points_block14 : ∀ (i : Fin 96) (x : Fin 16),
    pointCheck ((((i.castAdd 96).natAdd 192).natAdd 384).natAdd 768) x := by
  refine Fin.addCases (m := 48) (n := 48) ?_ ?_ <;>
    refine Fin.addCases (m := 24) (n := 24) ?_ ?_ <;>
      refine Fin.addCases (m := 12) (n := 12) ?_ ?_ <;>
        decide +kernel

private theorem points_block15 : ∀ (i : Fin 96) (x : Fin 16),
    pointCheck ((((i.natAdd 96).natAdd 192).natAdd 384).natAdd 768) x := by
  refine Fin.addCases (m := 48) (n := 48) ?_ ?_ <;>
    refine Fin.addCases (m := 24) (n := 24) ?_ ?_ <;>
      refine Fin.addCases (m := 12) (n := 12) ?_ ?_ <;>
        decide +kernel

private theorem points_checked : ∀ (i : Fin 1536) (x : Fin 16), pointCheck i x := by
  refine Fin.addCases (m := 768) (n := 768) ?_ ?_ <;>
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
  · exact points_block8
  · exact points_block9
  · exact points_block10
  · exact points_block11
  · exact points_block12
  · exact points_block13
  · exact points_block14
  · exact points_block15

/-- The selected conjugacy equation is checked in the faithful original
permutation image, using only the retained codes. -/
theorem conjugates_checked : ∀ (i : Fin 1536) (x : Fin 16),
    finFunctionFinEquiv.symm (certificate.rows (conjugatorRow i))
        (finFunctionFinEquiv.symm (certificate.rows i) x) =
      finFunctionFinEquiv.symm (certificate.rows (representativeRow (labelRow i)))
        (finFunctionFinEquiv.symm (certificate.rows (conjugatorRow i)) x) :=
  points_checked

/-- Conjugacy coverage is inside the original row group; the faithful
permutation action is used only to verify its equations. -/
def cover : FiniteConjugacyCover
    (fun i : Fin 1536 => (⟨i⟩ : Source)) 33 :=
  certificate.rowConjugacyCoverOfPoints
    PrimitiveAffineSixteenFrameRow27TopCertificate.rows_injective
    PrimitiveAffineSixteenFrameRow27TopCertificate.previousRow
    PrimitiveAffineSixteenFrameRow27TopCertificate.previous_checked
    representativeRow labelRow conjugatorRow conjugates_checked

/-- The cover uses precisely the representatives in the retained normal
transition certificates. -/
theorem representative_eq (j : Fin 33) :
    (⟨cover.representative j⟩ : Source) =
      PrimitiveAffineSixteenFrameRow27TopCertificate.representative j := by
  change (⟨representativeRow j⟩ : Source) =
    PrimitiveAffineSixteenFrameRow27TopCertificate.representative j
  fin_cases j <;> rfl

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow27ConjugacyCover

end
