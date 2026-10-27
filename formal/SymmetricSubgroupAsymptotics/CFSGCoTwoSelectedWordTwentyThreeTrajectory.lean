import SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoRelatorIdentities
import SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoCaches13
import SymmetricSubgroupAsymptotics.LinearMapSelectedKrylovPeriod
import Mathlib.Tactic.FinCases

/-! SAME documented W/e0/23; only the24 saved trajectory boundaries. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGCoTwoSelectedWordTwentyThreeTrajectory
open CFSGCoTwoLiteralRepresentation CFSGCoTwoNativeTwentyTwoRelatorIdentities
open MatrixNaturalRowDotReflection
private abbrev E := matrixWordEnd unitA unitB

def vectorCode (i : ℕ) : ℕ :=
  match i with
  | 0 => 1
  | 1 => 2250299
  | 2 => 2070574
  | 3 => 1730054
  | 4 => 1380985
  | 5 => 3078193
  | 6 => 2664684
  | 7 => 2703147
  | 8 => 2528742
  | 9 => 1174925
  | 10 => 560546
  | 11 => 1116032
  | 12 => 1296857
  | 13 => 633683
  | 14 => 1983374
  | 15 => 3489497
  | 16 => 3727130
  | 17 => 2197256
  | 18 => 2234617
  | 19 => 3348337
  | 20 => 2015528
  | 21 => 1939876
  | 22 => 603935
  | 23 => 1
  | _ => 0

def vectors (i : Fin 24) : Fin 22 → ZMod 2 :=
  fun j => (packedDigit 1 (vectorCode i.val) j.val : ZMod 2)

private theorem end_apply (v : Fin 22 → ZMod 2) : E v=CFSGCoTwoNativeTwentyTwoCaches13.Wp05_data.matrix 2 *ᵥ v := by
  change LinearRepresentationSelectedPrimePeriod.linearEnd
    (MonoidHom.id MatrixImage) (positiveWord unitA unitB) v=_
  rw [LinearRepresentationSelectedPrimePeriod.end_apply]
  exact congrArg (fun m : Matrix (Fin 22) (Fin 22) (ZMod 2) => m *ᵥ v)
    CFSGCoTwoNativeTwentyTwoRelatorIdentities.selectedWord_value

private theorem check_00 : ∀ i : Fin 22,
    packedDot 1 (CFSGCoTwoNativeTwentyTwoCaches13.binaryRowCode i.val) 1 22%2=packedDigit 1 2250299 i.val%2 := by decide +kernel

theorem step_00 : E (vectors 0)=vectors 1 := by
  rw [end_apply]
  exact LinearRepresentationSelectedPrimePeriod.packed_vector_step 2 22 1
    CFSGCoTwoNativeTwentyTwoCaches13.Wp05_digit CFSGCoTwoNativeTwentyTwoCaches13.binaryRowCode 1 2250299
    CFSGCoTwoNativeTwentyTwoCaches13.binary_row_binding check_00

private theorem check_01 : ∀ i : Fin 22,
    packedDot 1 (CFSGCoTwoNativeTwentyTwoCaches13.binaryRowCode i.val) 2250299 22%2=packedDigit 1 2070574 i.val%2 := by decide +kernel

theorem step_01 : E (vectors 1)=vectors 2 := by
  rw [end_apply]
  exact LinearRepresentationSelectedPrimePeriod.packed_vector_step 2 22 1
    CFSGCoTwoNativeTwentyTwoCaches13.Wp05_digit CFSGCoTwoNativeTwentyTwoCaches13.binaryRowCode 2250299 2070574
    CFSGCoTwoNativeTwentyTwoCaches13.binary_row_binding check_01

private theorem check_02 : ∀ i : Fin 22,
    packedDot 1 (CFSGCoTwoNativeTwentyTwoCaches13.binaryRowCode i.val) 2070574 22%2=packedDigit 1 1730054 i.val%2 := by decide +kernel

theorem step_02 : E (vectors 2)=vectors 3 := by
  rw [end_apply]
  exact LinearRepresentationSelectedPrimePeriod.packed_vector_step 2 22 1
    CFSGCoTwoNativeTwentyTwoCaches13.Wp05_digit CFSGCoTwoNativeTwentyTwoCaches13.binaryRowCode 2070574 1730054
    CFSGCoTwoNativeTwentyTwoCaches13.binary_row_binding check_02

private theorem check_03 : ∀ i : Fin 22,
    packedDot 1 (CFSGCoTwoNativeTwentyTwoCaches13.binaryRowCode i.val) 1730054 22%2=packedDigit 1 1380985 i.val%2 := by decide +kernel

theorem step_03 : E (vectors 3)=vectors 4 := by
  rw [end_apply]
  exact LinearRepresentationSelectedPrimePeriod.packed_vector_step 2 22 1
    CFSGCoTwoNativeTwentyTwoCaches13.Wp05_digit CFSGCoTwoNativeTwentyTwoCaches13.binaryRowCode 1730054 1380985
    CFSGCoTwoNativeTwentyTwoCaches13.binary_row_binding check_03

private theorem check_04 : ∀ i : Fin 22,
    packedDot 1 (CFSGCoTwoNativeTwentyTwoCaches13.binaryRowCode i.val) 1380985 22%2=packedDigit 1 3078193 i.val%2 := by decide +kernel

theorem step_04 : E (vectors 4)=vectors 5 := by
  rw [end_apply]
  exact LinearRepresentationSelectedPrimePeriod.packed_vector_step 2 22 1
    CFSGCoTwoNativeTwentyTwoCaches13.Wp05_digit CFSGCoTwoNativeTwentyTwoCaches13.binaryRowCode 1380985 3078193
    CFSGCoTwoNativeTwentyTwoCaches13.binary_row_binding check_04

private theorem check_05 : ∀ i : Fin 22,
    packedDot 1 (CFSGCoTwoNativeTwentyTwoCaches13.binaryRowCode i.val) 3078193 22%2=packedDigit 1 2664684 i.val%2 := by decide +kernel

theorem step_05 : E (vectors 5)=vectors 6 := by
  rw [end_apply]
  exact LinearRepresentationSelectedPrimePeriod.packed_vector_step 2 22 1
    CFSGCoTwoNativeTwentyTwoCaches13.Wp05_digit CFSGCoTwoNativeTwentyTwoCaches13.binaryRowCode 3078193 2664684
    CFSGCoTwoNativeTwentyTwoCaches13.binary_row_binding check_05

private theorem check_06 : ∀ i : Fin 22,
    packedDot 1 (CFSGCoTwoNativeTwentyTwoCaches13.binaryRowCode i.val) 2664684 22%2=packedDigit 1 2703147 i.val%2 := by decide +kernel

theorem step_06 : E (vectors 6)=vectors 7 := by
  rw [end_apply]
  exact LinearRepresentationSelectedPrimePeriod.packed_vector_step 2 22 1
    CFSGCoTwoNativeTwentyTwoCaches13.Wp05_digit CFSGCoTwoNativeTwentyTwoCaches13.binaryRowCode 2664684 2703147
    CFSGCoTwoNativeTwentyTwoCaches13.binary_row_binding check_06

private theorem check_07 : ∀ i : Fin 22,
    packedDot 1 (CFSGCoTwoNativeTwentyTwoCaches13.binaryRowCode i.val) 2703147 22%2=packedDigit 1 2528742 i.val%2 := by decide +kernel

theorem step_07 : E (vectors 7)=vectors 8 := by
  rw [end_apply]
  exact LinearRepresentationSelectedPrimePeriod.packed_vector_step 2 22 1
    CFSGCoTwoNativeTwentyTwoCaches13.Wp05_digit CFSGCoTwoNativeTwentyTwoCaches13.binaryRowCode 2703147 2528742
    CFSGCoTwoNativeTwentyTwoCaches13.binary_row_binding check_07

private theorem check_08 : ∀ i : Fin 22,
    packedDot 1 (CFSGCoTwoNativeTwentyTwoCaches13.binaryRowCode i.val) 2528742 22%2=packedDigit 1 1174925 i.val%2 := by decide +kernel

theorem step_08 : E (vectors 8)=vectors 9 := by
  rw [end_apply]
  exact LinearRepresentationSelectedPrimePeriod.packed_vector_step 2 22 1
    CFSGCoTwoNativeTwentyTwoCaches13.Wp05_digit CFSGCoTwoNativeTwentyTwoCaches13.binaryRowCode 2528742 1174925
    CFSGCoTwoNativeTwentyTwoCaches13.binary_row_binding check_08

private theorem check_09 : ∀ i : Fin 22,
    packedDot 1 (CFSGCoTwoNativeTwentyTwoCaches13.binaryRowCode i.val) 1174925 22%2=packedDigit 1 560546 i.val%2 := by decide +kernel

theorem step_09 : E (vectors 9)=vectors 10 := by
  rw [end_apply]
  exact LinearRepresentationSelectedPrimePeriod.packed_vector_step 2 22 1
    CFSGCoTwoNativeTwentyTwoCaches13.Wp05_digit CFSGCoTwoNativeTwentyTwoCaches13.binaryRowCode 1174925 560546
    CFSGCoTwoNativeTwentyTwoCaches13.binary_row_binding check_09

private theorem check_10 : ∀ i : Fin 22,
    packedDot 1 (CFSGCoTwoNativeTwentyTwoCaches13.binaryRowCode i.val) 560546 22%2=packedDigit 1 1116032 i.val%2 := by decide +kernel

theorem step_10 : E (vectors 10)=vectors 11 := by
  rw [end_apply]
  exact LinearRepresentationSelectedPrimePeriod.packed_vector_step 2 22 1
    CFSGCoTwoNativeTwentyTwoCaches13.Wp05_digit CFSGCoTwoNativeTwentyTwoCaches13.binaryRowCode 560546 1116032
    CFSGCoTwoNativeTwentyTwoCaches13.binary_row_binding check_10

private theorem check_11 : ∀ i : Fin 22,
    packedDot 1 (CFSGCoTwoNativeTwentyTwoCaches13.binaryRowCode i.val) 1116032 22%2=packedDigit 1 1296857 i.val%2 := by decide +kernel

theorem step_11 : E (vectors 11)=vectors 12 := by
  rw [end_apply]
  exact LinearRepresentationSelectedPrimePeriod.packed_vector_step 2 22 1
    CFSGCoTwoNativeTwentyTwoCaches13.Wp05_digit CFSGCoTwoNativeTwentyTwoCaches13.binaryRowCode 1116032 1296857
    CFSGCoTwoNativeTwentyTwoCaches13.binary_row_binding check_11

private theorem check_12 : ∀ i : Fin 22,
    packedDot 1 (CFSGCoTwoNativeTwentyTwoCaches13.binaryRowCode i.val) 1296857 22%2=packedDigit 1 633683 i.val%2 := by decide +kernel

theorem step_12 : E (vectors 12)=vectors 13 := by
  rw [end_apply]
  exact LinearRepresentationSelectedPrimePeriod.packed_vector_step 2 22 1
    CFSGCoTwoNativeTwentyTwoCaches13.Wp05_digit CFSGCoTwoNativeTwentyTwoCaches13.binaryRowCode 1296857 633683
    CFSGCoTwoNativeTwentyTwoCaches13.binary_row_binding check_12

private theorem check_13 : ∀ i : Fin 22,
    packedDot 1 (CFSGCoTwoNativeTwentyTwoCaches13.binaryRowCode i.val) 633683 22%2=packedDigit 1 1983374 i.val%2 := by decide +kernel

theorem step_13 : E (vectors 13)=vectors 14 := by
  rw [end_apply]
  exact LinearRepresentationSelectedPrimePeriod.packed_vector_step 2 22 1
    CFSGCoTwoNativeTwentyTwoCaches13.Wp05_digit CFSGCoTwoNativeTwentyTwoCaches13.binaryRowCode 633683 1983374
    CFSGCoTwoNativeTwentyTwoCaches13.binary_row_binding check_13

private theorem check_14 : ∀ i : Fin 22,
    packedDot 1 (CFSGCoTwoNativeTwentyTwoCaches13.binaryRowCode i.val) 1983374 22%2=packedDigit 1 3489497 i.val%2 := by decide +kernel

theorem step_14 : E (vectors 14)=vectors 15 := by
  rw [end_apply]
  exact LinearRepresentationSelectedPrimePeriod.packed_vector_step 2 22 1
    CFSGCoTwoNativeTwentyTwoCaches13.Wp05_digit CFSGCoTwoNativeTwentyTwoCaches13.binaryRowCode 1983374 3489497
    CFSGCoTwoNativeTwentyTwoCaches13.binary_row_binding check_14

private theorem check_15 : ∀ i : Fin 22,
    packedDot 1 (CFSGCoTwoNativeTwentyTwoCaches13.binaryRowCode i.val) 3489497 22%2=packedDigit 1 3727130 i.val%2 := by decide +kernel

theorem step_15 : E (vectors 15)=vectors 16 := by
  rw [end_apply]
  exact LinearRepresentationSelectedPrimePeriod.packed_vector_step 2 22 1
    CFSGCoTwoNativeTwentyTwoCaches13.Wp05_digit CFSGCoTwoNativeTwentyTwoCaches13.binaryRowCode 3489497 3727130
    CFSGCoTwoNativeTwentyTwoCaches13.binary_row_binding check_15

private theorem check_16 : ∀ i : Fin 22,
    packedDot 1 (CFSGCoTwoNativeTwentyTwoCaches13.binaryRowCode i.val) 3727130 22%2=packedDigit 1 2197256 i.val%2 := by decide +kernel

theorem step_16 : E (vectors 16)=vectors 17 := by
  rw [end_apply]
  exact LinearRepresentationSelectedPrimePeriod.packed_vector_step 2 22 1
    CFSGCoTwoNativeTwentyTwoCaches13.Wp05_digit CFSGCoTwoNativeTwentyTwoCaches13.binaryRowCode 3727130 2197256
    CFSGCoTwoNativeTwentyTwoCaches13.binary_row_binding check_16

private theorem check_17 : ∀ i : Fin 22,
    packedDot 1 (CFSGCoTwoNativeTwentyTwoCaches13.binaryRowCode i.val) 2197256 22%2=packedDigit 1 2234617 i.val%2 := by decide +kernel

theorem step_17 : E (vectors 17)=vectors 18 := by
  rw [end_apply]
  exact LinearRepresentationSelectedPrimePeriod.packed_vector_step 2 22 1
    CFSGCoTwoNativeTwentyTwoCaches13.Wp05_digit CFSGCoTwoNativeTwentyTwoCaches13.binaryRowCode 2197256 2234617
    CFSGCoTwoNativeTwentyTwoCaches13.binary_row_binding check_17

private theorem check_18 : ∀ i : Fin 22,
    packedDot 1 (CFSGCoTwoNativeTwentyTwoCaches13.binaryRowCode i.val) 2234617 22%2=packedDigit 1 3348337 i.val%2 := by decide +kernel

theorem step_18 : E (vectors 18)=vectors 19 := by
  rw [end_apply]
  exact LinearRepresentationSelectedPrimePeriod.packed_vector_step 2 22 1
    CFSGCoTwoNativeTwentyTwoCaches13.Wp05_digit CFSGCoTwoNativeTwentyTwoCaches13.binaryRowCode 2234617 3348337
    CFSGCoTwoNativeTwentyTwoCaches13.binary_row_binding check_18

private theorem check_19 : ∀ i : Fin 22,
    packedDot 1 (CFSGCoTwoNativeTwentyTwoCaches13.binaryRowCode i.val) 3348337 22%2=packedDigit 1 2015528 i.val%2 := by decide +kernel

theorem step_19 : E (vectors 19)=vectors 20 := by
  rw [end_apply]
  exact LinearRepresentationSelectedPrimePeriod.packed_vector_step 2 22 1
    CFSGCoTwoNativeTwentyTwoCaches13.Wp05_digit CFSGCoTwoNativeTwentyTwoCaches13.binaryRowCode 3348337 2015528
    CFSGCoTwoNativeTwentyTwoCaches13.binary_row_binding check_19

private theorem check_20 : ∀ i : Fin 22,
    packedDot 1 (CFSGCoTwoNativeTwentyTwoCaches13.binaryRowCode i.val) 2015528 22%2=packedDigit 1 1939876 i.val%2 := by decide +kernel

theorem step_20 : E (vectors 20)=vectors 21 := by
  rw [end_apply]
  exact LinearRepresentationSelectedPrimePeriod.packed_vector_step 2 22 1
    CFSGCoTwoNativeTwentyTwoCaches13.Wp05_digit CFSGCoTwoNativeTwentyTwoCaches13.binaryRowCode 2015528 1939876
    CFSGCoTwoNativeTwentyTwoCaches13.binary_row_binding check_20

private theorem check_21 : ∀ i : Fin 22,
    packedDot 1 (CFSGCoTwoNativeTwentyTwoCaches13.binaryRowCode i.val) 1939876 22%2=packedDigit 1 603935 i.val%2 := by decide +kernel

theorem step_21 : E (vectors 21)=vectors 22 := by
  rw [end_apply]
  exact LinearRepresentationSelectedPrimePeriod.packed_vector_step 2 22 1
    CFSGCoTwoNativeTwentyTwoCaches13.Wp05_digit CFSGCoTwoNativeTwentyTwoCaches13.binaryRowCode 1939876 603935
    CFSGCoTwoNativeTwentyTwoCaches13.binary_row_binding check_21

private theorem check_22 : ∀ i : Fin 22,
    packedDot 1 (CFSGCoTwoNativeTwentyTwoCaches13.binaryRowCode i.val) 603935 22%2=packedDigit 1 1 i.val%2 := by decide +kernel

theorem step_22 : E (vectors 22)=vectors 23 := by
  rw [end_apply]
  exact LinearRepresentationSelectedPrimePeriod.packed_vector_step 2 22 1
    CFSGCoTwoNativeTwentyTwoCaches13.Wp05_digit CFSGCoTwoNativeTwentyTwoCaches13.binaryRowCode 603935 1
    CFSGCoTwoNativeTwentyTwoCaches13.binary_row_binding check_22

theorem consecutive (i : Fin 23) : E (vectors i.castSucc)=vectors i.succ := by
  fin_cases i
  · exact step_00
  · exact step_01
  · exact step_02
  · exact step_03
  · exact step_04
  · exact step_05
  · exact step_06
  · exact step_07
  · exact step_08
  · exact step_09
  · exact step_10
  · exact step_11
  · exact step_12
  · exact step_13
  · exact step_14
  · exact step_15
  · exact step_16
  · exact step_17
  · exact step_18
  · exact step_19
  · exact step_20
  · exact step_21
  · exact step_22

theorem pow_initial (i : Fin 24) : (E^i.val) (vectors 0)=vectors i :=
  LinearMapSelectedKrylovPeriod.pow_apply_eq_vector E 23 vectors consecutive i

theorem return_twentyThree : (E^23) (vectors 0)=vectors 0 := by
  have h : (E^23) (vectors 0)=vectors 23 := pow_initial ⟨23,by decide⟩
  exact h.trans (show vectors 23=vectors 0 from rfl)

theorem nonreturn_one : E (vectors 0)≠vectors 0 := by
  have h : E (vectors 0)=vectors 1 := step_00
  have hn : vectors 1 (1 : Fin 22)≠vectors 0 1 := by decide +kernel
  intro he
  exact hn (congrFun (h.symm.trans he) 1)

end SymmetricSubgroupAsymptotics.CFSGCoTwoSelectedWordTwentyThreeTrajectory
