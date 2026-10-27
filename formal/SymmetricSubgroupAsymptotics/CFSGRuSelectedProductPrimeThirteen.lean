import SymmetricSubgroupAsymptotics.MatrixModelSelectedProductPrimePeriod
import SymmetricSubgroupAsymptotics.CFSGRuFirstPackedSourceColumns
import SymmetricSubgroupAsymptotics.CFSGRuSelectedSecondFourthRowPilot
import Mathlib.Tactic.FinCases

/-! ONE selected positive AB vector orbit:26 original matrix applications,
13 word applications,28 coordinates. No whole-matrix order is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGRuSelectedProductPrimeThirteen
open MatrixNaturalRowDotReflection MatrixModelSelectedProductPrimePeriod
open CFSG.Models.MatrixGroups.Ru
abbrev V := Fin 28 → ZMod 2
abbrev Model := CFSG.Models.MatrixGroups.Ru.Model

def firstRowCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 84939139
  | 1 => 85574168
  | 2 => 184392717
  | 3 => 84418247
  | 4 => 53745007
  | 5 => 40366483
  | 6 => 203407393
  | 7 => 257155371
  | 8 => 132491112
  | 9 => 7316447
  | 10 => 44168322
  | 11 => 226051366
  | 12 => 89055852
  | 13 => 96681907
  | 14 => 136041779
  | 15 => 74175814
  | 16 => 104758446
  | 17 => 39364308
  | 18 => 19238032
  | 19 => 32285467
  | 20 => 257706541
  | 21 => 90502945
  | 22 => 141396902
  | 23 => 141619908
  | 24 => 95393721
  | 25 => 255620944
  | 26 => 117615137
  | 27 => 133625304
  | _ => 0

def secondRowCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 172658611
  | 1 => 14019938
  | 2 => 53554120
  | 3 => 114259112
  | 4 => 77497393
  | 5 => 149367072
  | 6 => 73482723
  | 7 => 162087201
  | 8 => 204750753
  | 9 => 110529740
  | 10 => 23906216
  | 11 => 252804807
  | 12 => 125886263
  | 13 => 173098953
  | 14 => 218514713
  | 15 => 21597915
  | 16 => 36067822
  | 17 => 101593418
  | 18 => 207421632
  | 19 => 247294840
  | 20 => 14481185
  | 21 => 203951345
  | 22 => 211468017
  | 23 => 155378214
  | 24 => 132582773
  | 25 => 10117594
  | 26 => 148156748
  | 27 => 123760620
  | _ => 0

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 1
  | 1 => 24181201
  | 2 => 111403798
  | 3 => 132244891
  | 4 => 39819846
  | 5 => 103947576
  | 6 => 92291972
  | 7 => 218665987
  | 8 => 161431641
  | 9 => 2342077
  | 10 => 192187893
  | 11 => 186771059
  | 12 => 234091045
  | 13 => 174337369
  | 14 => 62258116
  | 15 => 240419620
  | 16 => 238614573
  | 17 => 254333793
  | 18 => 249505773
  | 19 => 64460733
  | 20 => 130430202
  | 21 => 85942160
  | 22 => 247756228
  | 23 => 95027204
  | 24 => 207722706
  | 25 => 87581437
  | 26 => 1
  | _ => 0

def vectorCode (code : ℕ) (i : Fin 28) : ZMod 2 := packedDigit 1 code i.val

def vectors (i : Fin 14) : V := vectorCode (stageCode (2*i.val))
def middle (i : Fin 13) : V := vectorCode (stageCode (2*i.val+1))

private theorem first_transpose : ∀ i j : Fin 28,
    packedDigit 1 (CFSGRuFirstPackedSourceColumns.columnCode j.val) i.val=
      packedDigit 1 (firstRowCode i.val) j.val := by decide +kernel
private theorem second_transpose : ∀ i j : Fin 28,
    packedDigit 1 (CFSGRuSelectedSecondFourthRowPilot.columnCode j.val) i.val=
      packedDigit 1 (secondRowCode i.val) j.val := by decide +kernel

theorem first_row_binding (i j : Fin 28) :
    rawDigit rows1 i.val j.val=packedDigit 1 (firstRowCode i.val) j.val :=
  (CFSGRuFirstPackedSourceColumns.source_column_binding j i).trans (first_transpose i j)
theorem second_row_binding (i j : Fin 28) :
    rawDigit rows2 i.val j.val=packedDigit 1 (secondRowCode i.val) j.val :=
  (CFSGRuSelectedSecondFourthRowPilot.source_column_binding j i).trans (second_transpose i j)

theorem packed_step_0 : ∀ z : Fin 28,
    packedDot 1 (secondRowCode z.val) (stageCode 0) 28 % 2=
      packedDigit 1 (stageCode 1) z.val % 2 := by decide +kernel

theorem packed_step_1 : ∀ z : Fin 28,
    packedDot 1 (firstRowCode z.val) (stageCode 1) 28 % 2=
      packedDigit 1 (stageCode 2) z.val % 2 := by decide +kernel

theorem packed_step_2 : ∀ z : Fin 28,
    packedDot 1 (secondRowCode z.val) (stageCode 2) 28 % 2=
      packedDigit 1 (stageCode 3) z.val % 2 := by decide +kernel

theorem packed_step_3 : ∀ z : Fin 28,
    packedDot 1 (firstRowCode z.val) (stageCode 3) 28 % 2=
      packedDigit 1 (stageCode 4) z.val % 2 := by decide +kernel

theorem packed_step_4 : ∀ z : Fin 28,
    packedDot 1 (secondRowCode z.val) (stageCode 4) 28 % 2=
      packedDigit 1 (stageCode 5) z.val % 2 := by decide +kernel

theorem packed_step_5 : ∀ z : Fin 28,
    packedDot 1 (firstRowCode z.val) (stageCode 5) 28 % 2=
      packedDigit 1 (stageCode 6) z.val % 2 := by decide +kernel

theorem packed_step_6 : ∀ z : Fin 28,
    packedDot 1 (secondRowCode z.val) (stageCode 6) 28 % 2=
      packedDigit 1 (stageCode 7) z.val % 2 := by decide +kernel

theorem packed_step_7 : ∀ z : Fin 28,
    packedDot 1 (firstRowCode z.val) (stageCode 7) 28 % 2=
      packedDigit 1 (stageCode 8) z.val % 2 := by decide +kernel

theorem packed_step_8 : ∀ z : Fin 28,
    packedDot 1 (secondRowCode z.val) (stageCode 8) 28 % 2=
      packedDigit 1 (stageCode 9) z.val % 2 := by decide +kernel

theorem packed_step_9 : ∀ z : Fin 28,
    packedDot 1 (firstRowCode z.val) (stageCode 9) 28 % 2=
      packedDigit 1 (stageCode 10) z.val % 2 := by decide +kernel

theorem packed_step_10 : ∀ z : Fin 28,
    packedDot 1 (secondRowCode z.val) (stageCode 10) 28 % 2=
      packedDigit 1 (stageCode 11) z.val % 2 := by decide +kernel

theorem packed_step_11 : ∀ z : Fin 28,
    packedDot 1 (firstRowCode z.val) (stageCode 11) 28 % 2=
      packedDigit 1 (stageCode 12) z.val % 2 := by decide +kernel

theorem packed_step_12 : ∀ z : Fin 28,
    packedDot 1 (secondRowCode z.val) (stageCode 12) 28 % 2=
      packedDigit 1 (stageCode 13) z.val % 2 := by decide +kernel

theorem packed_step_13 : ∀ z : Fin 28,
    packedDot 1 (firstRowCode z.val) (stageCode 13) 28 % 2=
      packedDigit 1 (stageCode 14) z.val % 2 := by decide +kernel

theorem packed_step_14 : ∀ z : Fin 28,
    packedDot 1 (secondRowCode z.val) (stageCode 14) 28 % 2=
      packedDigit 1 (stageCode 15) z.val % 2 := by decide +kernel

theorem packed_step_15 : ∀ z : Fin 28,
    packedDot 1 (firstRowCode z.val) (stageCode 15) 28 % 2=
      packedDigit 1 (stageCode 16) z.val % 2 := by decide +kernel

theorem packed_step_16 : ∀ z : Fin 28,
    packedDot 1 (secondRowCode z.val) (stageCode 16) 28 % 2=
      packedDigit 1 (stageCode 17) z.val % 2 := by decide +kernel

theorem packed_step_17 : ∀ z : Fin 28,
    packedDot 1 (firstRowCode z.val) (stageCode 17) 28 % 2=
      packedDigit 1 (stageCode 18) z.val % 2 := by decide +kernel

theorem packed_step_18 : ∀ z : Fin 28,
    packedDot 1 (secondRowCode z.val) (stageCode 18) 28 % 2=
      packedDigit 1 (stageCode 19) z.val % 2 := by decide +kernel

theorem packed_step_19 : ∀ z : Fin 28,
    packedDot 1 (firstRowCode z.val) (stageCode 19) 28 % 2=
      packedDigit 1 (stageCode 20) z.val % 2 := by decide +kernel

theorem packed_step_20 : ∀ z : Fin 28,
    packedDot 1 (secondRowCode z.val) (stageCode 20) 28 % 2=
      packedDigit 1 (stageCode 21) z.val % 2 := by decide +kernel

theorem packed_step_21 : ∀ z : Fin 28,
    packedDot 1 (firstRowCode z.val) (stageCode 21) 28 % 2=
      packedDigit 1 (stageCode 22) z.val % 2 := by decide +kernel

theorem packed_step_22 : ∀ z : Fin 28,
    packedDot 1 (secondRowCode z.val) (stageCode 22) 28 % 2=
      packedDigit 1 (stageCode 23) z.val % 2 := by decide +kernel

theorem packed_step_23 : ∀ z : Fin 28,
    packedDot 1 (firstRowCode z.val) (stageCode 23) 28 % 2=
      packedDigit 1 (stageCode 24) z.val % 2 := by decide +kernel

theorem packed_step_24 : ∀ z : Fin 28,
    packedDot 1 (secondRowCode z.val) (stageCode 24) 28 % 2=
      packedDigit 1 (stageCode 25) z.val % 2 := by decide +kernel

theorem packed_step_25 : ∀ z : Fin 28,
    packedDot 1 (firstRowCode z.val) (stageCode 25) 28 % 2=
      packedDigit 1 (stageCode 26) z.val % 2 := by decide +kernel

theorem b_step (i : Fin 13) :
    CFSG.Models.MatrixData.matrix 2 28 rows2 *ᵥ vectors i.castSucc=middle i := by
  apply packed_vector_step 2 28 1 rows2 secondRowCode
    (stageCode (2*i.val)) (stageCode (2*i.val+1)) second_row_binding
  fin_cases i
  · exact packed_step_0
  · exact packed_step_2
  · exact packed_step_4
  · exact packed_step_6
  · exact packed_step_8
  · exact packed_step_10
  · exact packed_step_12
  · exact packed_step_14
  · exact packed_step_16
  · exact packed_step_18
  · exact packed_step_20
  · exact packed_step_22
  · exact packed_step_24

theorem a_step (i : Fin 13) :
    CFSG.Models.MatrixData.matrix 2 28 rows1 *ᵥ middle i=vectors i.succ := by
  change CFSG.Models.MatrixData.matrix 2 28 rows1 *ᵥ vectorCode (stageCode (2*i.val+1))=
    vectorCode (stageCode (2*(i.val+1)))
  have he : 2*(i.val+1)=2*i.val+2 := by omega
  rw [he]
  apply packed_vector_step 2 28 1 rows1 firstRowCode
    (stageCode (2*i.val+1)) (stageCode (2*i.val+2)) first_row_binding
  fin_cases i
  · exact packed_step_1
  · exact packed_step_3
  · exact packed_step_5
  · exact packed_step_7
  · exact packed_step_9
  · exact packed_step_11
  · exact packed_step_13
  · exact packed_step_15
  · exact packed_step_17
  · exact packed_step_19
  · exact packed_step_21
  · exact packed_step_23
  · exact packed_step_25

def wordEnd : Module.End (ZMod 2) V := productEnd 2 28 rows1 rows2

theorem consecutive (i : Fin 13) : wordEnd (vectors i.castSucc)=vectors i.succ := by
  change CFSG.Models.MatrixData.matrix 2 28 rows1 *ᵥ
    (CFSG.Models.MatrixData.matrix 2 28 rows2 *ᵥ vectors i.castSucc)=vectors i.succ
  rw [b_step,a_step]

theorem pow_initial (i : Fin 14) : (wordEnd^i.val) (vectors 0)=vectors i :=
  LinearMapSelectedKrylovPeriod.pow_apply_eq_vector wordEnd 13 vectors consecutive i

theorem return_thirteen : (wordEnd^13) (vectors 0)=vectors 0 := by
  have h : (wordEnd^13) (vectors 0)=vectors 13 := pow_initial ⟨13,by decide⟩
  exact h.trans (show vectors 13=vectors 0 from rfl)

theorem nonreturn_one : wordEnd (vectors 0)≠vectors 0 := by
  have h : wordEnd (vectors 0)=vectors 1 := by simpa only [pow_one] using pow_initial ⟨1,by decide⟩
  have hn : vectors 1 (0 : Fin 28)≠vectors 0 0 := by decide +kernel
  intro he
  exact hn (congrFun (h.symm.trans he) 0)

theorem exists_thirteen_dvd_orderOf (hn : ¬IsMulCommutative Model) :
    ∃ g : Model, 13 ∣ orderOf g :=
  MatrixModelSelectedProductPrimePeriod.exists_prime_dvd_orderOf 2 28 rows1 rows2 13
    (by decide) (vectors 0) return_thirteen nonreturn_one hn

theorem thirteen_dvd_card (hn : ¬IsMulCommutative Model) : 13 ∣ Nat.card Model :=
  MatrixModelSelectedProductPrimePeriod.prime_dvd_card 2 28 rows1 rows2 13
    (by decide) (vectors 0) return_thirteen nonreturn_one hn

end SymmetricSubgroupAsymptotics.CFSGRuSelectedProductPrimeThirteen
