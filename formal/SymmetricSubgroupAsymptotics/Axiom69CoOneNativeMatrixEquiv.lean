import SymmetricSubgroupAsymptotics.Axiom69NativeMatrixDefinitionPort
import SymmetricSubgroupAsymptotics.MatrixSeedMonoidUnitsEquivalence
import SymmetricSubgroupAsymptotics.External.CFSG.Models.MatrixGroups.Co1
import SymmetricSubgroupAsymptotics.Axiom69ModeOneDecoderSemantics

/-! Actual Co1 seed compatibility, using ONLY a local definition port of
AxiomMath/CFSG69cb972 NativeSporadic and its exact two raw source files.
The621-byte seeds are byte-identical to our frozen ATLAS inputs. The two shared
entry-list comparisons below establish the semantic matrix equalities; their
SHA records alone are not used as mathematical assumptions. No upstream
4.35 theorem is imported and no named-group identification is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Axiom69CoOneNativeMatrixEquiv
open Axiom69NativeMatrixDefinitionPort

def firstSeed : String := " 1     2    24    24\n011001001011001001111011\n010010011110110010100001\n010111101000000010101111\n110001101110100101110100\n010101101100110001110110\n101111010000001000001101\n101110001011101001111010\n001010000011101010000001\n010100111100000101110101\n110000000100010111111001\n101001011001101001010110\n101001111110110010101011\n110001100111010000101000\n100101111011101111010111\n100101110110001000101000\n110111110100000111010011\n000111100010000111011001\n100010011110100111101100\n010010101110011101010111\n000010110000001010010001\n001101111000000100101001\n110111111100000110100110\n010101110011101101011101\n010001000000110111111101\n"

def secondSeed : String := " 1     2    24    24\n111101000111000010000110\n110110010011011100000111\n000101100001000000101101\n111110010110010010000110\n110000100010010111001110\n100100101010001001100011\n001011001101011010011111\n000110011001110111010111\n000011100110110111110110\n001011110010011110010100\n001000000101010001101001\n110110000101001111001000\n001000110000100001000110\n101011011000110001010100\n010110011111100111011101\n110111100001001101000010\n101101100110011110000011\n111100000110011101001010\n110100111010000010000111\n101100101101010000111111\n010010101010000001000100\n011100100100001110010100\n100110101100010110101000\n101001000010101000100011\n"

/-- Local port of the new native Co1 carrier. This is NOT an imported
upstream4.35 declaration or a claim that a new theorem has been ported. -/
abbrev Model : Type := (seedMonoid 2 24 1 firstSeed secondSeed)ˣ

private theorem first_entries_check :
    (Axiom69ModeOneDecoderSemantics.modeOneEntries firstSeed ==
      Axiom69ModeOneDecoderSemantics.expectedEntries 24 CFSG.Models.MatrixGroups.Co1.rows1) = true := by
  decide +kernel

private theorem second_entries_check :
    (Axiom69ModeOneDecoderSemantics.modeOneEntries secondSeed ==
      Axiom69ModeOneDecoderSemantics.expectedEntries 24 CFSG.Models.MatrixGroups.Co1.rows2) = true := by
  decide +kernel

theorem first_seed_eq : decode 2 24 1 firstSeed =
    CFSG.Models.MatrixData.matrix 2 24 CFSG.Models.MatrixGroups.Co1.rows1 :=
  Axiom69ModeOneDecoderSemantics.matrix_eq_of_entries 2 24 firstSeed
    CFSG.Models.MatrixGroups.Co1.rows1 (by simpa only [beq_iff_eq] using first_entries_check)

theorem second_seed_eq : decode 2 24 1 secondSeed =
    CFSG.Models.MatrixData.matrix 2 24 CFSG.Models.MatrixGroups.Co1.rows2 :=
  Axiom69ModeOneDecoderSemantics.matrix_eq_of_entries 2 24 secondSeed
    CFSG.Models.MatrixGroups.Co1.rows2 (by simpa only [beq_iff_eq] using second_entries_check)

/-- The actual decoded positive-word unit group is equivalent to the
SAME old native24/F2 model, without seed invertibility premises. -/
def equiv : Model ≃* CFSG.Models.MatrixGroups.Co1.Model :=
  MatrixSeedMonoidUnitsEquivalence.equiv_of_decoded_eq 2 24
    CFSG.Models.MatrixGroups.Co1.rows1 CFSG.Models.MatrixGroups.Co1.rows2
    (decode 2 24 1 firstSeed) (decode 2 24 1 secondSeed)
    first_seed_eq second_seed_eq

-- Once semantic seed equalities are proved, subsequent value transport
-- must not normalize the621-byte source strings or native row literals.
attribute [local irreducible] firstSeed secondSeed
  Axiom69NativeMatrixDefinitionPort.decode CFSG.Models.MatrixData.matrix
  CFSG.Models.MatrixGroups.Co1.rows1 CFSG.Models.MatrixGroups.Co1.rows2

/-- Elements retain their actual24-by24 matrix under this equivalence. -/
theorem equiv_value (x : Model) :
    (((equiv x : CFSG.Models.MatrixGroups.Co1.Model) :
      Matrix.GeneralLinearGroup (Fin 24) (ZMod 2)) : Matrix (Fin 24) (Fin 24) (ZMod 2)) =
        ((x : seedMonoid 2 24 1 firstSeed secondSeed) : Matrix (Fin 24) (Fin 24) (ZMod 2)) :=
  MatrixSeedMonoidUnitsEquivalence.equiv_of_decoded_eq_value 2 24
    CFSG.Models.MatrixGroups.Co1.rows1 CFSG.Models.MatrixGroups.Co1.rows2
    (decode 2 24 1 firstSeed) (decode 2 24 1 secondSeed)
    first_seed_eq second_seed_eq x

end SymmetricSubgroupAsymptotics.Axiom69CoOneNativeMatrixEquiv
