import SymmetricSubgroupAsymptotics.External.CFSG.Models.MatrixGroups.Ru
import SymmetricSubgroupAsymptotics.MatrixModelSelectedPointPeriodTwo
import Mathlib.Tactic.FinCases

/-! A selected vector-period certificate for the first pinned Ru generator.
Its return after two steps and one-coordinate nonreturn bind to the
actual model through the shared genuine-unit bridge. No whole matrix
square, inverse or group-order certificate is required. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGRuSelectedVectorPeriodTwo

abbrev Model := CFSG.Models.MatrixGroups.Ru.Model
abbrev V := Fin 28 → ZMod 2

def initial : V := Pi.single (0 : Fin 28) 1

def firstEnd : Module.End (ZMod 2) V :=
  MatrixModelSelectedPointPeriodTwo.firstEnd 2 28 CFSG.Models.MatrixGroups.Ru.rows1

theorem vector_return_two : (firstEnd ^ 2) initial = initial := by
  change CFSG.Models.MatrixData.matrix 2 28 CFSG.Models.MatrixGroups.Ru.rows1 *ᵥ
    (CFSG.Models.MatrixData.matrix 2 28 CFSG.Models.MatrixGroups.Ru.rows1 *ᵥ
      Pi.single (0 : Fin 28) 1) = initial
  rw [Matrix.mulVec_single_one]
  funext j
  fin_cases j <;> decide +kernel

theorem vector_nonreturn_one : firstEnd initial ≠ initial := by
  have hne : (firstEnd initial) (2 : Fin 28) ≠ initial 2 := by
    decide +kernel
  intro h
  exact hne (congrFun h (2 : Fin 28))

theorem exists_two_dvd_orderOf (hn : ¬IsMulCommutative Model) :
    ∃ g : Model, 2 ∣ orderOf g :=
  MatrixModelSelectedPointPeriodTwo.exists_two_dvd_orderOf 2 28
    CFSG.Models.MatrixGroups.Ru.rows1 CFSG.Models.MatrixGroups.Ru.rows2 initial
    vector_return_two vector_nonreturn_one hn

theorem even_card (hn : ¬IsMulCommutative Model) : Even (Nat.card Model) :=
  MatrixModelSelectedPointPeriodTwo.even_card_of_first_vector_period_two 2 28
    CFSG.Models.MatrixGroups.Ru.rows1 CFSG.Models.MatrixGroups.Ru.rows2 initial
    vector_return_two vector_nonreturn_one hn

end SymmetricSubgroupAsymptotics.CFSGRuSelectedVectorPeriodTwo
