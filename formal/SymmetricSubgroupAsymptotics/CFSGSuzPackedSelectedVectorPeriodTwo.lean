import SymmetricSubgroupAsymptotics.CFSGSuzPackedRows00To07
import SymmetricSubgroupAsymptotics.CFSGSuzPackedRows08To15
import SymmetricSubgroupAsymptotics.CFSGSuzPackedRows16To23
import SymmetricSubgroupAsymptotics.CFSGSuzPackedRows24To31
import SymmetricSubgroupAsymptotics.CFSGSuzPackedRows32To39
import SymmetricSubgroupAsymptotics.CFSGSuzPackedRows40To47
import SymmetricSubgroupAsymptotics.CFSGSuzPackedRows48To55
import SymmetricSubgroupAsymptotics.CFSGSuzPackedRows56To63
import SymmetricSubgroupAsymptotics.MatrixModelSelectedPointPeriodTwo
import Mathlib.Tactic.FinCases

/-! Full two-step return on ONE basis vector; no full matrix square.
Generated from one hash-guarded first Suz matrix and its first column only.
Literal data require the closed kernel bindings and scalar checks below.
No resource limit is raised. The checked row-zero pilot supplies the shared
column and row-zero theorem; its source bytes are guarded by the producer. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGSuzPackedSelectedVectorPeriodTwo
open MatrixNaturalRowDotReflection
open CFSGSuzPackedRowZeroPilot

abbrev Model := CFSG.Models.MatrixGroups.Suz.Model
abbrev V := Fin 64 → ZMod 3

def initial : V := Pi.single (0 : Fin 64) 1

def firstEnd : Module.End (ZMod 3) V :=
  MatrixModelSelectedPointPeriodTwo.firstEnd 3 64 CFSG.Models.MatrixGroups.Suz.rows1

theorem coordinate_eq_initial (i : Fin 64)
    (h : (a *ᵥ (fun j => a j 0)) i = if i = 0 then 1 else 0) :
    (a *ᵥ (fun j => a j 0)) i = initial i := by
  simpa only [initial,Pi.single_apply] using h

theorem return_coordinate (i : Fin 64) :
    (a *ᵥ (fun j => a j 0)) i = initial i := by
  apply coordinate_eq_initial
  fin_cases i
  · exact CFSGSuzPackedRows00To07.actual_row_00_dot
  · exact CFSGSuzPackedRows00To07.actual_row_01_dot
  · exact CFSGSuzPackedRows00To07.actual_row_02_dot
  · exact CFSGSuzPackedRows00To07.actual_row_03_dot
  · exact CFSGSuzPackedRows00To07.actual_row_04_dot
  · exact CFSGSuzPackedRows00To07.actual_row_05_dot
  · exact CFSGSuzPackedRows00To07.actual_row_06_dot
  · exact CFSGSuzPackedRows00To07.actual_row_07_dot
  · exact CFSGSuzPackedRows08To15.actual_row_08_dot
  · exact CFSGSuzPackedRows08To15.actual_row_09_dot
  · exact CFSGSuzPackedRows08To15.actual_row_10_dot
  · exact CFSGSuzPackedRows08To15.actual_row_11_dot
  · exact CFSGSuzPackedRows08To15.actual_row_12_dot
  · exact CFSGSuzPackedRows08To15.actual_row_13_dot
  · exact CFSGSuzPackedRows08To15.actual_row_14_dot
  · exact CFSGSuzPackedRows08To15.actual_row_15_dot
  · exact CFSGSuzPackedRows16To23.actual_row_16_dot
  · exact CFSGSuzPackedRows16To23.actual_row_17_dot
  · exact CFSGSuzPackedRows16To23.actual_row_18_dot
  · exact CFSGSuzPackedRows16To23.actual_row_19_dot
  · exact CFSGSuzPackedRows16To23.actual_row_20_dot
  · exact CFSGSuzPackedRows16To23.actual_row_21_dot
  · exact CFSGSuzPackedRows16To23.actual_row_22_dot
  · exact CFSGSuzPackedRows16To23.actual_row_23_dot
  · exact CFSGSuzPackedRows24To31.actual_row_24_dot
  · exact CFSGSuzPackedRows24To31.actual_row_25_dot
  · exact CFSGSuzPackedRows24To31.actual_row_26_dot
  · exact CFSGSuzPackedRows24To31.actual_row_27_dot
  · exact CFSGSuzPackedRows24To31.actual_row_28_dot
  · exact CFSGSuzPackedRows24To31.actual_row_29_dot
  · exact CFSGSuzPackedRows24To31.actual_row_30_dot
  · exact CFSGSuzPackedRows24To31.actual_row_31_dot
  · exact CFSGSuzPackedRows32To39.actual_row_32_dot
  · exact CFSGSuzPackedRows32To39.actual_row_33_dot
  · exact CFSGSuzPackedRows32To39.actual_row_34_dot
  · exact CFSGSuzPackedRows32To39.actual_row_35_dot
  · exact CFSGSuzPackedRows32To39.actual_row_36_dot
  · exact CFSGSuzPackedRows32To39.actual_row_37_dot
  · exact CFSGSuzPackedRows32To39.actual_row_38_dot
  · exact CFSGSuzPackedRows32To39.actual_row_39_dot
  · exact CFSGSuzPackedRows40To47.actual_row_40_dot
  · exact CFSGSuzPackedRows40To47.actual_row_41_dot
  · exact CFSGSuzPackedRows40To47.actual_row_42_dot
  · exact CFSGSuzPackedRows40To47.actual_row_43_dot
  · exact CFSGSuzPackedRows40To47.actual_row_44_dot
  · exact CFSGSuzPackedRows40To47.actual_row_45_dot
  · exact CFSGSuzPackedRows40To47.actual_row_46_dot
  · exact CFSGSuzPackedRows40To47.actual_row_47_dot
  · exact CFSGSuzPackedRows48To55.actual_row_48_dot
  · exact CFSGSuzPackedRows48To55.actual_row_49_dot
  · exact CFSGSuzPackedRows48To55.actual_row_50_dot
  · exact CFSGSuzPackedRows48To55.actual_row_51_dot
  · exact CFSGSuzPackedRows48To55.actual_row_52_dot
  · exact CFSGSuzPackedRows48To55.actual_row_53_dot
  · exact CFSGSuzPackedRows48To55.actual_row_54_dot
  · exact CFSGSuzPackedRows48To55.actual_row_55_dot
  · exact CFSGSuzPackedRows56To63.actual_row_56_dot
  · exact CFSGSuzPackedRows56To63.actual_row_57_dot
  · exact CFSGSuzPackedRows56To63.actual_row_58_dot
  · exact CFSGSuzPackedRows56To63.actual_row_59_dot
  · exact CFSGSuzPackedRows56To63.actual_row_60_dot
  · exact CFSGSuzPackedRows56To63.actual_row_61_dot
  · exact CFSGSuzPackedRows56To63.actual_row_62_dot
  · exact CFSGSuzPackedRows56To63.actual_row_63_dot

theorem vector_return_two : (firstEnd ^ 2) initial = initial := by
  rw [pow_two, Module.End.mul_apply]
  simp only [firstEnd, MatrixModelSelectedPointPeriodTwo.firstEnd, Matrix.mulVecLin_apply]
  change a *ᵥ (a *ᵥ Pi.single (0 : Fin 64) 1) = initial
  rw [Matrix.mulVec_single_one]
  funext i
  exact return_coordinate i

theorem vector_nonreturn_one : firstEnd initial ≠ initial := by
  intro h
  change a *ᵥ Pi.single (0 : Fin 64) 1 = initial at h
  rw [Matrix.mulVec_single_one] at h
  have hc : a (0 : Fin 64) 0 = initial 0 := congrFun h 0
  have hne : a (0 : Fin 64) 0 ≠ initial 0 := by decide +kernel
  exact hne hc

theorem exists_two_dvd_orderOf (hn : ¬IsMulCommutative Model) :
    ∃ g : Model, 2 ∣ orderOf g :=
  MatrixModelSelectedPointPeriodTwo.exists_two_dvd_orderOf 3 64
    CFSG.Models.MatrixGroups.Suz.rows1 CFSG.Models.MatrixGroups.Suz.rows2 initial
    vector_return_two vector_nonreturn_one hn

theorem even_card (hn : ¬IsMulCommutative Model) : Even (Nat.card Model) :=
  MatrixModelSelectedPointPeriodTwo.even_card_of_first_vector_period_two 3 64
    CFSG.Models.MatrixGroups.Suz.rows1 CFSG.Models.MatrixGroups.Suz.rows2 initial
    vector_return_two vector_nonreturn_one hn

end SymmetricSubgroupAsymptotics.CFSGSuzPackedSelectedVectorPeriodTwo
