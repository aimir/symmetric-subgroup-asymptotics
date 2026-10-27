import SymmetricSubgroupAsymptotics.MatrixModelSelectedPositiveWordPrimePeriod
import SymmetricSubgroupAsymptotics.External.CFSG.Models.MatrixGroups.Ly

/-! Exact original positive Ly word ABABABB from the frozen guide.
This proves only its literal-vector semantics, with NO order/period claim. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGLySelectedPositiveSevenWord
open CFSG.Models.MatrixGroups.Ly
open MatrixModelSelectedPointPeriodTwo

abbrev V := Fin 111 → ZMod 5

def actualWord : List Bool := [true,false,true,false,true,false,false]

def selectedEnd : Module.End (ZMod 5) V :=
  firstEnd 5 111 rows1 * firstEnd 5 111 rows2 * firstEnd 5 111 rows1 *
    firstEnd 5 111 rows2 * firstEnd 5 111 rows1 *
      firstEnd 5 111 rows2 * firstEnd 5 111 rows2

theorem wordEnd_binding :
    MatrixModelSelectedPositiveWordPrimePeriod.wordEnd 5 111 rows1 rows2 actualWord=
      selectedEnd := by
  simp [actualWord,MatrixModelSelectedPositiveWordPrimePeriod.wordEnd,
    MatrixModelSelectedPositiveWordPrimePeriod.letterEnd,selectedEnd,mul_assoc]

theorem selectedEnd_apply (v : V) : selectedEnd v=
    CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
      (CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
        (CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
          (CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
            (CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
              (CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
                (CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ v)))))) := by
  simp only [selectedEnd,Module.End.mul_apply,firstEnd,Matrix.mulVecLin_apply]

end SymmetricSubgroupAsymptotics.CFSGLySelectedPositiveSevenWord
