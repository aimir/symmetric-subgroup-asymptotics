import SymmetricSubgroupAsymptotics.MatrixModelSelectedPositiveWordPrimePeriod
import SymmetricSubgroupAsymptotics.External.CFSG.Models.MatrixGroups.ON

/-! Exact positive original ON word AB. This file binds only the literal
word and its vector action; no period or group order is asserted. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGONSelectedProductWord
open CFSG.Models.MatrixGroups.ON
open MatrixModelSelectedPointPeriodTwo

abbrev V := Fin 154 → ZMod 3

def actualWord : List Bool := [true,false]

def selectedEnd : Module.End (ZMod 3) V :=
  firstEnd 3 154 rows1 * firstEnd 3 154 rows2

theorem wordEnd_binding :
    MatrixModelSelectedPositiveWordPrimePeriod.wordEnd 3 154 rows1 rows2 actualWord=
      selectedEnd := by
  simp [actualWord,MatrixModelSelectedPositiveWordPrimePeriod.wordEnd,
    MatrixModelSelectedPositiveWordPrimePeriod.letterEnd,selectedEnd,mul_assoc]

theorem selectedEnd_apply (v : V) : selectedEnd v=
    CFSG.Models.MatrixData.matrix 3 154 rows1 *ᵥ
      (CFSG.Models.MatrixData.matrix 3 154 rows2 *ᵥ v) := by
  simp only [selectedEnd,Module.End.mul_apply,firstEnd,Matrix.mulVecLin_apply]

end SymmetricSubgroupAsymptotics.CFSGONSelectedProductWord
