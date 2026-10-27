import SymmetricSubgroupAsymptotics.MatrixModelSelectedPositiveWordPrimePeriod
import SymmetricSubgroupAsymptotics.External.CFSG.Models.MatrixGroups.Co1

/-! The fixed positive 23-letter original Co1 word suggested by upstream w0.
This binds the positive word directly; it neither identifies it with a signed
word nor assumes whole A²/B³ identities or a word order. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGCoOneSelectedUpstreamPositiveWord
open CFSG.Models.MatrixGroups.Co1
open MatrixModelSelectedPointPeriodTwo

abbrev V := Fin 24 → ZMod 2

def actualWord : List Bool := [false,false,true,false,false,true,false,true,false,true,false,false,true,false,false,true,true,false,false,false,true,false,false]

def selectedEnd : Module.End (ZMod 2) V :=
  firstEnd 2 24 rows2 *
    firstEnd 2 24 rows2 *
    firstEnd 2 24 rows1 *
    firstEnd 2 24 rows2 *
    firstEnd 2 24 rows2 *
    firstEnd 2 24 rows1 *
    firstEnd 2 24 rows2 *
    firstEnd 2 24 rows1 *
    firstEnd 2 24 rows2 *
    firstEnd 2 24 rows1 *
    firstEnd 2 24 rows2 *
    firstEnd 2 24 rows2 *
    firstEnd 2 24 rows1 *
    firstEnd 2 24 rows2 *
    firstEnd 2 24 rows2 *
    firstEnd 2 24 rows1 *
    firstEnd 2 24 rows1 *
    firstEnd 2 24 rows2 *
    firstEnd 2 24 rows2 *
    firstEnd 2 24 rows2 *
    firstEnd 2 24 rows1 *
    firstEnd 2 24 rows2 *
    firstEnd 2 24 rows2

theorem wordEnd_binding :
    MatrixModelSelectedPositiveWordPrimePeriod.wordEnd 2 24 rows1 rows2 actualWord =
      selectedEnd := by
  simp [actualWord,MatrixModelSelectedPositiveWordPrimePeriod.wordEnd,
    MatrixModelSelectedPositiveWordPrimePeriod.letterEnd,selectedEnd,mul_assoc]

theorem selectedEnd_apply (v : V) : selectedEnd v =
    (CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ (CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ (CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ (CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ (CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ (CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ (CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ (CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ (CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ (CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ (CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ (CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ (CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ (CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ (CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ (CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ (CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ (CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ (CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ (CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ (CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ (CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ (CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ v))))))))))))))))))))))) := by
  simp only [selectedEnd,Module.End.mul_apply,firstEnd,Matrix.mulVecLin_apply]

end SymmetricSubgroupAsymptotics.CFSGCoOneSelectedUpstreamPositiveWord
