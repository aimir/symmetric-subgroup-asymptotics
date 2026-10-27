import SymmetricSubgroupAsymptotics.MatrixModelSelectedPositiveWordPrimePeriod
import SymmetricSubgroupAsymptotics.External.CFSG.Models.MatrixGroups.HN

/-! Exact positive original HN word (AB)^2. This file binds only the
literal word and its vector action; it asserts no period or group order. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGHNSelectedProductSquareWord
open CFSG.Models.MatrixGroups.HN
open MatrixModelSelectedPointPeriodTwo

abbrev V := Fin 133 → ZMod 5

def actualWord : List Bool := [true,false,true,false]

def selectedEnd : Module.End (ZMod 5) V :=
  firstEnd 5 133 rows1 * firstEnd 5 133 rows2 *
    firstEnd 5 133 rows1 * firstEnd 5 133 rows2

theorem wordEnd_binding :
    MatrixModelSelectedPositiveWordPrimePeriod.wordEnd 5 133 rows1 rows2 actualWord=
      selectedEnd := by
  simp [actualWord,MatrixModelSelectedPositiveWordPrimePeriod.wordEnd,
    MatrixModelSelectedPositiveWordPrimePeriod.letterEnd,selectedEnd,mul_assoc]

theorem selectedEnd_apply (v : V) : selectedEnd v=
    CFSG.Models.MatrixData.matrix 5 133 rows1 *ᵥ
      (CFSG.Models.MatrixData.matrix 5 133 rows2 *ᵥ
        (CFSG.Models.MatrixData.matrix 5 133 rows1 *ᵥ
          (CFSG.Models.MatrixData.matrix 5 133 rows2 *ᵥ v))) := by
  simp only [selectedEnd,Module.End.mul_apply,firstEnd,Matrix.mulVecLin_apply]

end SymmetricSubgroupAsymptotics.CFSGHNSelectedProductSquareWord
