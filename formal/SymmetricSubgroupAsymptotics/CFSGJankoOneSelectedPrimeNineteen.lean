import SymmetricSubgroupAsymptotics.CFSGJankoOneCommwordLinearBinding
import SymmetricSubgroupAsymptotics.LinearMapSelectedKrylovPeriod
import Mathlib.Tactic.FinCases

/-! ONE selected actual J1 word/e0 prime19 orbit. Ninety-five original
matrix-vector steps are separately checked. No whole-word order claimed. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGJankoOneSelectedPrimeNineteen
open CFSGJankoOneSevenMatrices CFSGJankoOneCommwordLinearBinding
open MatrixNaturalRowDotReflection

def firstRowCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 159029616
  | 1 => 70467847
  | 2 => 40075801
  | 3 => 6400073
  | 4 => 26743610
  | 5 => 51996215
  | 6 => 3211849
  | _ => 0

def secondRowCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 42303861
  | 1 => 137562698
  | 2 => 18978981
  | 3 => 153183026
  | 4 => 58337095
  | 5 => 87179411
  | 6 => 155792195
  | _ => 0

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 1
  | 1 => 53945765
  | 2 => 42303861
  | 3 => 88693073
  | 4 => 153241360
  | 5 => 73746001
  | 6 => 69543445
  | 7 => 2556964
  | 8 => 169898562
  | 9 => 72564896
  | 10 => 61354265
  | 11 => 111710309
  | 12 => 22258183
  | 13 => 136458646
  | 14 => 175531110
  | 15 => 52992353
  | 16 => 26640931
  | 17 => 55117073
  | 18 => 2592906
  | 19 => 105292377
  | 20 => 39998554
  | 21 => 90809892
  | 22 => 161695331
  | 23 => 144067205
  | 24 => 157712474
  | 25 => 33755284
  | 26 => 137589536
  | 27 => 103310247
  | 28 => 39164562
  | 29 => 105468740
  | 30 => 38032968
  | 31 => 28821
  | 32 => 104342161
  | 33 => 9077889
  | 34 => 109585985
  | 35 => 50881620
  | 36 => 119632474
  | 37 => 54101106
  | 38 => 103388585
  | 39 => 177441409
  | 40 => 57694277
  | 41 => 76182601
  | 42 => 51589394
  | 43 => 135934072
  | 44 => 125924208
  | 45 => 76767892
  | 46 => 106440616
  | 47 => 108496677
  | 48 => 128021123
  | 49 => 67535976
  | 50 => 3493972
  | 51 => 92837233
  | 52 => 36205827
  | 53 => 126103872
  | 54 => 89351048
  | 55 => 123082597
  | 56 => 37103649
  | 57 => 72908946
  | 58 => 2325024
  | 59 => 104105249
  | 60 => 123033108
  | 61 => 19092025
  | 62 => 87236905
  | 63 => 67331589
  | 64 => 78267011
  | 65 => 73897048
  | 66 => 137664032
  | 67 => 135946921
  | 68 => 104417282
  | 69 => 36244106
  | 70 => 51656452
  | 71 => 174535272
  | 72 => 158344978
  | 73 => 40405657
  | 74 => 8745370
  | 75 => 50806890
  | 76 => 42304064
  | 77 => 153380912
  | 78 => 88775319
  | 79 => 25694504
  | 80 => 70714417
  | 81 => 108488505
  | 82 => 50942868
  | 83 => 174199594
  | 84 => 104211978
  | 85 => 123953465
  | 86 => 156243333
  | 87 => 25245865
  | 88 => 137889858
  | 89 => 75650117
  | 90 => 125199713
  | 91 => 124389938
  | 92 => 91649626
  | 93 => 109253273
  | 94 => 159029616
  | 95 => 1
  | _ => 0

def stageVector (k : ℕ) : V := fun j => packedDigit 4 (stageCode k) j.val

def vectors (i : Fin 20) : V := stageVector (5*i.val)

theorem first_row_binding : ∀ i j : Fin 7,
    rawA i j=packedDigit 4 (firstRowCode i.val) j.val := by decide +kernel

theorem second_row_binding : ∀ i j : Fin 7,
    rawB i j=packedDigit 4 (secondRowCode i.val) j.val := by decide +kernel

private theorem check_0 : ∀ i : Fin 7,
    packedDot 4 (secondRowCode i.val) (stageCode 0) 7 % 11=
      packedDigit 4 (stageCode 1) i.val % 11 := by decide +kernel

private theorem step_0 : matrixB *ᵥ stageVector 0=stageVector 1 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawB secondRowCode (stageCode 0) (stageCode 1) second_row_binding check_0

private theorem check_1 : ∀ i : Fin 7,
    packedDot 4 (secondRowCode i.val) (stageCode 1) 7 % 11=
      packedDigit 4 (stageCode 2) i.val % 11 := by decide +kernel

private theorem step_1 : matrixB *ᵥ stageVector 1=stageVector 2 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawB secondRowCode (stageCode 1) (stageCode 2) second_row_binding check_1

private theorem check_2 : ∀ i : Fin 7,
    packedDot 4 (firstRowCode i.val) (stageCode 2) 7 % 11=
      packedDigit 4 (stageCode 3) i.val % 11 := by decide +kernel

private theorem step_2 : matrixA *ᵥ stageVector 2=stageVector 3 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawA firstRowCode (stageCode 2) (stageCode 3) first_row_binding check_2

private theorem check_3 : ∀ i : Fin 7,
    packedDot 4 (secondRowCode i.val) (stageCode 3) 7 % 11=
      packedDigit 4 (stageCode 4) i.val % 11 := by decide +kernel

private theorem step_3 : matrixB *ᵥ stageVector 3=stageVector 4 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawB secondRowCode (stageCode 3) (stageCode 4) second_row_binding check_3

private theorem check_4 : ∀ i : Fin 7,
    packedDot 4 (firstRowCode i.val) (stageCode 4) 7 % 11=
      packedDigit 4 (stageCode 5) i.val % 11 := by decide +kernel

private theorem step_4 : matrixA *ᵥ stageVector 4=stageVector 5 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawA firstRowCode (stageCode 4) (stageCode 5) first_row_binding check_4

private theorem check_5 : ∀ i : Fin 7,
    packedDot 4 (secondRowCode i.val) (stageCode 5) 7 % 11=
      packedDigit 4 (stageCode 6) i.val % 11 := by decide +kernel

private theorem step_5 : matrixB *ᵥ stageVector 5=stageVector 6 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawB secondRowCode (stageCode 5) (stageCode 6) second_row_binding check_5

private theorem check_6 : ∀ i : Fin 7,
    packedDot 4 (secondRowCode i.val) (stageCode 6) 7 % 11=
      packedDigit 4 (stageCode 7) i.val % 11 := by decide +kernel

private theorem step_6 : matrixB *ᵥ stageVector 6=stageVector 7 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawB secondRowCode (stageCode 6) (stageCode 7) second_row_binding check_6

private theorem check_7 : ∀ i : Fin 7,
    packedDot 4 (firstRowCode i.val) (stageCode 7) 7 % 11=
      packedDigit 4 (stageCode 8) i.val % 11 := by decide +kernel

private theorem step_7 : matrixA *ᵥ stageVector 7=stageVector 8 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawA firstRowCode (stageCode 7) (stageCode 8) first_row_binding check_7

private theorem check_8 : ∀ i : Fin 7,
    packedDot 4 (secondRowCode i.val) (stageCode 8) 7 % 11=
      packedDigit 4 (stageCode 9) i.val % 11 := by decide +kernel

private theorem step_8 : matrixB *ᵥ stageVector 8=stageVector 9 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawB secondRowCode (stageCode 8) (stageCode 9) second_row_binding check_8

private theorem check_9 : ∀ i : Fin 7,
    packedDot 4 (firstRowCode i.val) (stageCode 9) 7 % 11=
      packedDigit 4 (stageCode 10) i.val % 11 := by decide +kernel

private theorem step_9 : matrixA *ᵥ stageVector 9=stageVector 10 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawA firstRowCode (stageCode 9) (stageCode 10) first_row_binding check_9

private theorem check_10 : ∀ i : Fin 7,
    packedDot 4 (secondRowCode i.val) (stageCode 10) 7 % 11=
      packedDigit 4 (stageCode 11) i.val % 11 := by decide +kernel

private theorem step_10 : matrixB *ᵥ stageVector 10=stageVector 11 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawB secondRowCode (stageCode 10) (stageCode 11) second_row_binding check_10

private theorem check_11 : ∀ i : Fin 7,
    packedDot 4 (secondRowCode i.val) (stageCode 11) 7 % 11=
      packedDigit 4 (stageCode 12) i.val % 11 := by decide +kernel

private theorem step_11 : matrixB *ᵥ stageVector 11=stageVector 12 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawB secondRowCode (stageCode 11) (stageCode 12) second_row_binding check_11

private theorem check_12 : ∀ i : Fin 7,
    packedDot 4 (firstRowCode i.val) (stageCode 12) 7 % 11=
      packedDigit 4 (stageCode 13) i.val % 11 := by decide +kernel

private theorem step_12 : matrixA *ᵥ stageVector 12=stageVector 13 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawA firstRowCode (stageCode 12) (stageCode 13) first_row_binding check_12

private theorem check_13 : ∀ i : Fin 7,
    packedDot 4 (secondRowCode i.val) (stageCode 13) 7 % 11=
      packedDigit 4 (stageCode 14) i.val % 11 := by decide +kernel

private theorem step_13 : matrixB *ᵥ stageVector 13=stageVector 14 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawB secondRowCode (stageCode 13) (stageCode 14) second_row_binding check_13

private theorem check_14 : ∀ i : Fin 7,
    packedDot 4 (firstRowCode i.val) (stageCode 14) 7 % 11=
      packedDigit 4 (stageCode 15) i.val % 11 := by decide +kernel

private theorem step_14 : matrixA *ᵥ stageVector 14=stageVector 15 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawA firstRowCode (stageCode 14) (stageCode 15) first_row_binding check_14

private theorem check_15 : ∀ i : Fin 7,
    packedDot 4 (secondRowCode i.val) (stageCode 15) 7 % 11=
      packedDigit 4 (stageCode 16) i.val % 11 := by decide +kernel

private theorem step_15 : matrixB *ᵥ stageVector 15=stageVector 16 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawB secondRowCode (stageCode 15) (stageCode 16) second_row_binding check_15

private theorem check_16 : ∀ i : Fin 7,
    packedDot 4 (secondRowCode i.val) (stageCode 16) 7 % 11=
      packedDigit 4 (stageCode 17) i.val % 11 := by decide +kernel

private theorem step_16 : matrixB *ᵥ stageVector 16=stageVector 17 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawB secondRowCode (stageCode 16) (stageCode 17) second_row_binding check_16

private theorem check_17 : ∀ i : Fin 7,
    packedDot 4 (firstRowCode i.val) (stageCode 17) 7 % 11=
      packedDigit 4 (stageCode 18) i.val % 11 := by decide +kernel

private theorem step_17 : matrixA *ᵥ stageVector 17=stageVector 18 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawA firstRowCode (stageCode 17) (stageCode 18) first_row_binding check_17

private theorem check_18 : ∀ i : Fin 7,
    packedDot 4 (secondRowCode i.val) (stageCode 18) 7 % 11=
      packedDigit 4 (stageCode 19) i.val % 11 := by decide +kernel

private theorem step_18 : matrixB *ᵥ stageVector 18=stageVector 19 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawB secondRowCode (stageCode 18) (stageCode 19) second_row_binding check_18

private theorem check_19 : ∀ i : Fin 7,
    packedDot 4 (firstRowCode i.val) (stageCode 19) 7 % 11=
      packedDigit 4 (stageCode 20) i.val % 11 := by decide +kernel

private theorem step_19 : matrixA *ᵥ stageVector 19=stageVector 20 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawA firstRowCode (stageCode 19) (stageCode 20) first_row_binding check_19

private theorem check_20 : ∀ i : Fin 7,
    packedDot 4 (secondRowCode i.val) (stageCode 20) 7 % 11=
      packedDigit 4 (stageCode 21) i.val % 11 := by decide +kernel

private theorem step_20 : matrixB *ᵥ stageVector 20=stageVector 21 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawB secondRowCode (stageCode 20) (stageCode 21) second_row_binding check_20

private theorem check_21 : ∀ i : Fin 7,
    packedDot 4 (secondRowCode i.val) (stageCode 21) 7 % 11=
      packedDigit 4 (stageCode 22) i.val % 11 := by decide +kernel

private theorem step_21 : matrixB *ᵥ stageVector 21=stageVector 22 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawB secondRowCode (stageCode 21) (stageCode 22) second_row_binding check_21

private theorem check_22 : ∀ i : Fin 7,
    packedDot 4 (firstRowCode i.val) (stageCode 22) 7 % 11=
      packedDigit 4 (stageCode 23) i.val % 11 := by decide +kernel

private theorem step_22 : matrixA *ᵥ stageVector 22=stageVector 23 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawA firstRowCode (stageCode 22) (stageCode 23) first_row_binding check_22

private theorem check_23 : ∀ i : Fin 7,
    packedDot 4 (secondRowCode i.val) (stageCode 23) 7 % 11=
      packedDigit 4 (stageCode 24) i.val % 11 := by decide +kernel

private theorem step_23 : matrixB *ᵥ stageVector 23=stageVector 24 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawB secondRowCode (stageCode 23) (stageCode 24) second_row_binding check_23

private theorem check_24 : ∀ i : Fin 7,
    packedDot 4 (firstRowCode i.val) (stageCode 24) 7 % 11=
      packedDigit 4 (stageCode 25) i.val % 11 := by decide +kernel

private theorem step_24 : matrixA *ᵥ stageVector 24=stageVector 25 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawA firstRowCode (stageCode 24) (stageCode 25) first_row_binding check_24

private theorem check_25 : ∀ i : Fin 7,
    packedDot 4 (secondRowCode i.val) (stageCode 25) 7 % 11=
      packedDigit 4 (stageCode 26) i.val % 11 := by decide +kernel

private theorem step_25 : matrixB *ᵥ stageVector 25=stageVector 26 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawB secondRowCode (stageCode 25) (stageCode 26) second_row_binding check_25

private theorem check_26 : ∀ i : Fin 7,
    packedDot 4 (secondRowCode i.val) (stageCode 26) 7 % 11=
      packedDigit 4 (stageCode 27) i.val % 11 := by decide +kernel

private theorem step_26 : matrixB *ᵥ stageVector 26=stageVector 27 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawB secondRowCode (stageCode 26) (stageCode 27) second_row_binding check_26

private theorem check_27 : ∀ i : Fin 7,
    packedDot 4 (firstRowCode i.val) (stageCode 27) 7 % 11=
      packedDigit 4 (stageCode 28) i.val % 11 := by decide +kernel

private theorem step_27 : matrixA *ᵥ stageVector 27=stageVector 28 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawA firstRowCode (stageCode 27) (stageCode 28) first_row_binding check_27

private theorem check_28 : ∀ i : Fin 7,
    packedDot 4 (secondRowCode i.val) (stageCode 28) 7 % 11=
      packedDigit 4 (stageCode 29) i.val % 11 := by decide +kernel

private theorem step_28 : matrixB *ᵥ stageVector 28=stageVector 29 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawB secondRowCode (stageCode 28) (stageCode 29) second_row_binding check_28

private theorem check_29 : ∀ i : Fin 7,
    packedDot 4 (firstRowCode i.val) (stageCode 29) 7 % 11=
      packedDigit 4 (stageCode 30) i.val % 11 := by decide +kernel

private theorem step_29 : matrixA *ᵥ stageVector 29=stageVector 30 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawA firstRowCode (stageCode 29) (stageCode 30) first_row_binding check_29

private theorem check_30 : ∀ i : Fin 7,
    packedDot 4 (secondRowCode i.val) (stageCode 30) 7 % 11=
      packedDigit 4 (stageCode 31) i.val % 11 := by decide +kernel

private theorem step_30 : matrixB *ᵥ stageVector 30=stageVector 31 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawB secondRowCode (stageCode 30) (stageCode 31) second_row_binding check_30

private theorem check_31 : ∀ i : Fin 7,
    packedDot 4 (secondRowCode i.val) (stageCode 31) 7 % 11=
      packedDigit 4 (stageCode 32) i.val % 11 := by decide +kernel

private theorem step_31 : matrixB *ᵥ stageVector 31=stageVector 32 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawB secondRowCode (stageCode 31) (stageCode 32) second_row_binding check_31

private theorem check_32 : ∀ i : Fin 7,
    packedDot 4 (firstRowCode i.val) (stageCode 32) 7 % 11=
      packedDigit 4 (stageCode 33) i.val % 11 := by decide +kernel

private theorem step_32 : matrixA *ᵥ stageVector 32=stageVector 33 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawA firstRowCode (stageCode 32) (stageCode 33) first_row_binding check_32

private theorem check_33 : ∀ i : Fin 7,
    packedDot 4 (secondRowCode i.val) (stageCode 33) 7 % 11=
      packedDigit 4 (stageCode 34) i.val % 11 := by decide +kernel

private theorem step_33 : matrixB *ᵥ stageVector 33=stageVector 34 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawB secondRowCode (stageCode 33) (stageCode 34) second_row_binding check_33

private theorem check_34 : ∀ i : Fin 7,
    packedDot 4 (firstRowCode i.val) (stageCode 34) 7 % 11=
      packedDigit 4 (stageCode 35) i.val % 11 := by decide +kernel

private theorem step_34 : matrixA *ᵥ stageVector 34=stageVector 35 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawA firstRowCode (stageCode 34) (stageCode 35) first_row_binding check_34

private theorem check_35 : ∀ i : Fin 7,
    packedDot 4 (secondRowCode i.val) (stageCode 35) 7 % 11=
      packedDigit 4 (stageCode 36) i.val % 11 := by decide +kernel

private theorem step_35 : matrixB *ᵥ stageVector 35=stageVector 36 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawB secondRowCode (stageCode 35) (stageCode 36) second_row_binding check_35

private theorem check_36 : ∀ i : Fin 7,
    packedDot 4 (secondRowCode i.val) (stageCode 36) 7 % 11=
      packedDigit 4 (stageCode 37) i.val % 11 := by decide +kernel

private theorem step_36 : matrixB *ᵥ stageVector 36=stageVector 37 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawB secondRowCode (stageCode 36) (stageCode 37) second_row_binding check_36

private theorem check_37 : ∀ i : Fin 7,
    packedDot 4 (firstRowCode i.val) (stageCode 37) 7 % 11=
      packedDigit 4 (stageCode 38) i.val % 11 := by decide +kernel

private theorem step_37 : matrixA *ᵥ stageVector 37=stageVector 38 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawA firstRowCode (stageCode 37) (stageCode 38) first_row_binding check_37

private theorem check_38 : ∀ i : Fin 7,
    packedDot 4 (secondRowCode i.val) (stageCode 38) 7 % 11=
      packedDigit 4 (stageCode 39) i.val % 11 := by decide +kernel

private theorem step_38 : matrixB *ᵥ stageVector 38=stageVector 39 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawB secondRowCode (stageCode 38) (stageCode 39) second_row_binding check_38

private theorem check_39 : ∀ i : Fin 7,
    packedDot 4 (firstRowCode i.val) (stageCode 39) 7 % 11=
      packedDigit 4 (stageCode 40) i.val % 11 := by decide +kernel

private theorem step_39 : matrixA *ᵥ stageVector 39=stageVector 40 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawA firstRowCode (stageCode 39) (stageCode 40) first_row_binding check_39

private theorem check_40 : ∀ i : Fin 7,
    packedDot 4 (secondRowCode i.val) (stageCode 40) 7 % 11=
      packedDigit 4 (stageCode 41) i.val % 11 := by decide +kernel

private theorem step_40 : matrixB *ᵥ stageVector 40=stageVector 41 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawB secondRowCode (stageCode 40) (stageCode 41) second_row_binding check_40

private theorem check_41 : ∀ i : Fin 7,
    packedDot 4 (secondRowCode i.val) (stageCode 41) 7 % 11=
      packedDigit 4 (stageCode 42) i.val % 11 := by decide +kernel

private theorem step_41 : matrixB *ᵥ stageVector 41=stageVector 42 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawB secondRowCode (stageCode 41) (stageCode 42) second_row_binding check_41

private theorem check_42 : ∀ i : Fin 7,
    packedDot 4 (firstRowCode i.val) (stageCode 42) 7 % 11=
      packedDigit 4 (stageCode 43) i.val % 11 := by decide +kernel

private theorem step_42 : matrixA *ᵥ stageVector 42=stageVector 43 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawA firstRowCode (stageCode 42) (stageCode 43) first_row_binding check_42

private theorem check_43 : ∀ i : Fin 7,
    packedDot 4 (secondRowCode i.val) (stageCode 43) 7 % 11=
      packedDigit 4 (stageCode 44) i.val % 11 := by decide +kernel

private theorem step_43 : matrixB *ᵥ stageVector 43=stageVector 44 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawB secondRowCode (stageCode 43) (stageCode 44) second_row_binding check_43

private theorem check_44 : ∀ i : Fin 7,
    packedDot 4 (firstRowCode i.val) (stageCode 44) 7 % 11=
      packedDigit 4 (stageCode 45) i.val % 11 := by decide +kernel

private theorem step_44 : matrixA *ᵥ stageVector 44=stageVector 45 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawA firstRowCode (stageCode 44) (stageCode 45) first_row_binding check_44

private theorem check_45 : ∀ i : Fin 7,
    packedDot 4 (secondRowCode i.val) (stageCode 45) 7 % 11=
      packedDigit 4 (stageCode 46) i.val % 11 := by decide +kernel

private theorem step_45 : matrixB *ᵥ stageVector 45=stageVector 46 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawB secondRowCode (stageCode 45) (stageCode 46) second_row_binding check_45

private theorem check_46 : ∀ i : Fin 7,
    packedDot 4 (secondRowCode i.val) (stageCode 46) 7 % 11=
      packedDigit 4 (stageCode 47) i.val % 11 := by decide +kernel

private theorem step_46 : matrixB *ᵥ stageVector 46=stageVector 47 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawB secondRowCode (stageCode 46) (stageCode 47) second_row_binding check_46

private theorem check_47 : ∀ i : Fin 7,
    packedDot 4 (firstRowCode i.val) (stageCode 47) 7 % 11=
      packedDigit 4 (stageCode 48) i.val % 11 := by decide +kernel

private theorem step_47 : matrixA *ᵥ stageVector 47=stageVector 48 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawA firstRowCode (stageCode 47) (stageCode 48) first_row_binding check_47

private theorem check_48 : ∀ i : Fin 7,
    packedDot 4 (secondRowCode i.val) (stageCode 48) 7 % 11=
      packedDigit 4 (stageCode 49) i.val % 11 := by decide +kernel

private theorem step_48 : matrixB *ᵥ stageVector 48=stageVector 49 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawB secondRowCode (stageCode 48) (stageCode 49) second_row_binding check_48

private theorem check_49 : ∀ i : Fin 7,
    packedDot 4 (firstRowCode i.val) (stageCode 49) 7 % 11=
      packedDigit 4 (stageCode 50) i.val % 11 := by decide +kernel

private theorem step_49 : matrixA *ᵥ stageVector 49=stageVector 50 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawA firstRowCode (stageCode 49) (stageCode 50) first_row_binding check_49

private theorem check_50 : ∀ i : Fin 7,
    packedDot 4 (secondRowCode i.val) (stageCode 50) 7 % 11=
      packedDigit 4 (stageCode 51) i.val % 11 := by decide +kernel

private theorem step_50 : matrixB *ᵥ stageVector 50=stageVector 51 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawB secondRowCode (stageCode 50) (stageCode 51) second_row_binding check_50

private theorem check_51 : ∀ i : Fin 7,
    packedDot 4 (secondRowCode i.val) (stageCode 51) 7 % 11=
      packedDigit 4 (stageCode 52) i.val % 11 := by decide +kernel

private theorem step_51 : matrixB *ᵥ stageVector 51=stageVector 52 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawB secondRowCode (stageCode 51) (stageCode 52) second_row_binding check_51

private theorem check_52 : ∀ i : Fin 7,
    packedDot 4 (firstRowCode i.val) (stageCode 52) 7 % 11=
      packedDigit 4 (stageCode 53) i.val % 11 := by decide +kernel

private theorem step_52 : matrixA *ᵥ stageVector 52=stageVector 53 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawA firstRowCode (stageCode 52) (stageCode 53) first_row_binding check_52

private theorem check_53 : ∀ i : Fin 7,
    packedDot 4 (secondRowCode i.val) (stageCode 53) 7 % 11=
      packedDigit 4 (stageCode 54) i.val % 11 := by decide +kernel

private theorem step_53 : matrixB *ᵥ stageVector 53=stageVector 54 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawB secondRowCode (stageCode 53) (stageCode 54) second_row_binding check_53

private theorem check_54 : ∀ i : Fin 7,
    packedDot 4 (firstRowCode i.val) (stageCode 54) 7 % 11=
      packedDigit 4 (stageCode 55) i.val % 11 := by decide +kernel

private theorem step_54 : matrixA *ᵥ stageVector 54=stageVector 55 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawA firstRowCode (stageCode 54) (stageCode 55) first_row_binding check_54

private theorem check_55 : ∀ i : Fin 7,
    packedDot 4 (secondRowCode i.val) (stageCode 55) 7 % 11=
      packedDigit 4 (stageCode 56) i.val % 11 := by decide +kernel

private theorem step_55 : matrixB *ᵥ stageVector 55=stageVector 56 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawB secondRowCode (stageCode 55) (stageCode 56) second_row_binding check_55

private theorem check_56 : ∀ i : Fin 7,
    packedDot 4 (secondRowCode i.val) (stageCode 56) 7 % 11=
      packedDigit 4 (stageCode 57) i.val % 11 := by decide +kernel

private theorem step_56 : matrixB *ᵥ stageVector 56=stageVector 57 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawB secondRowCode (stageCode 56) (stageCode 57) second_row_binding check_56

private theorem check_57 : ∀ i : Fin 7,
    packedDot 4 (firstRowCode i.val) (stageCode 57) 7 % 11=
      packedDigit 4 (stageCode 58) i.val % 11 := by decide +kernel

private theorem step_57 : matrixA *ᵥ stageVector 57=stageVector 58 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawA firstRowCode (stageCode 57) (stageCode 58) first_row_binding check_57

private theorem check_58 : ∀ i : Fin 7,
    packedDot 4 (secondRowCode i.val) (stageCode 58) 7 % 11=
      packedDigit 4 (stageCode 59) i.val % 11 := by decide +kernel

private theorem step_58 : matrixB *ᵥ stageVector 58=stageVector 59 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawB secondRowCode (stageCode 58) (stageCode 59) second_row_binding check_58

private theorem check_59 : ∀ i : Fin 7,
    packedDot 4 (firstRowCode i.val) (stageCode 59) 7 % 11=
      packedDigit 4 (stageCode 60) i.val % 11 := by decide +kernel

private theorem step_59 : matrixA *ᵥ stageVector 59=stageVector 60 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawA firstRowCode (stageCode 59) (stageCode 60) first_row_binding check_59

private theorem check_60 : ∀ i : Fin 7,
    packedDot 4 (secondRowCode i.val) (stageCode 60) 7 % 11=
      packedDigit 4 (stageCode 61) i.val % 11 := by decide +kernel

private theorem step_60 : matrixB *ᵥ stageVector 60=stageVector 61 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawB secondRowCode (stageCode 60) (stageCode 61) second_row_binding check_60

private theorem check_61 : ∀ i : Fin 7,
    packedDot 4 (secondRowCode i.val) (stageCode 61) 7 % 11=
      packedDigit 4 (stageCode 62) i.val % 11 := by decide +kernel

private theorem step_61 : matrixB *ᵥ stageVector 61=stageVector 62 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawB secondRowCode (stageCode 61) (stageCode 62) second_row_binding check_61

private theorem check_62 : ∀ i : Fin 7,
    packedDot 4 (firstRowCode i.val) (stageCode 62) 7 % 11=
      packedDigit 4 (stageCode 63) i.val % 11 := by decide +kernel

private theorem step_62 : matrixA *ᵥ stageVector 62=stageVector 63 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawA firstRowCode (stageCode 62) (stageCode 63) first_row_binding check_62

private theorem check_63 : ∀ i : Fin 7,
    packedDot 4 (secondRowCode i.val) (stageCode 63) 7 % 11=
      packedDigit 4 (stageCode 64) i.val % 11 := by decide +kernel

private theorem step_63 : matrixB *ᵥ stageVector 63=stageVector 64 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawB secondRowCode (stageCode 63) (stageCode 64) second_row_binding check_63

private theorem check_64 : ∀ i : Fin 7,
    packedDot 4 (firstRowCode i.val) (stageCode 64) 7 % 11=
      packedDigit 4 (stageCode 65) i.val % 11 := by decide +kernel

private theorem step_64 : matrixA *ᵥ stageVector 64=stageVector 65 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawA firstRowCode (stageCode 64) (stageCode 65) first_row_binding check_64

private theorem check_65 : ∀ i : Fin 7,
    packedDot 4 (secondRowCode i.val) (stageCode 65) 7 % 11=
      packedDigit 4 (stageCode 66) i.val % 11 := by decide +kernel

private theorem step_65 : matrixB *ᵥ stageVector 65=stageVector 66 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawB secondRowCode (stageCode 65) (stageCode 66) second_row_binding check_65

private theorem check_66 : ∀ i : Fin 7,
    packedDot 4 (secondRowCode i.val) (stageCode 66) 7 % 11=
      packedDigit 4 (stageCode 67) i.val % 11 := by decide +kernel

private theorem step_66 : matrixB *ᵥ stageVector 66=stageVector 67 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawB secondRowCode (stageCode 66) (stageCode 67) second_row_binding check_66

private theorem check_67 : ∀ i : Fin 7,
    packedDot 4 (firstRowCode i.val) (stageCode 67) 7 % 11=
      packedDigit 4 (stageCode 68) i.val % 11 := by decide +kernel

private theorem step_67 : matrixA *ᵥ stageVector 67=stageVector 68 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawA firstRowCode (stageCode 67) (stageCode 68) first_row_binding check_67

private theorem check_68 : ∀ i : Fin 7,
    packedDot 4 (secondRowCode i.val) (stageCode 68) 7 % 11=
      packedDigit 4 (stageCode 69) i.val % 11 := by decide +kernel

private theorem step_68 : matrixB *ᵥ stageVector 68=stageVector 69 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawB secondRowCode (stageCode 68) (stageCode 69) second_row_binding check_68

private theorem check_69 : ∀ i : Fin 7,
    packedDot 4 (firstRowCode i.val) (stageCode 69) 7 % 11=
      packedDigit 4 (stageCode 70) i.val % 11 := by decide +kernel

private theorem step_69 : matrixA *ᵥ stageVector 69=stageVector 70 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawA firstRowCode (stageCode 69) (stageCode 70) first_row_binding check_69

private theorem check_70 : ∀ i : Fin 7,
    packedDot 4 (secondRowCode i.val) (stageCode 70) 7 % 11=
      packedDigit 4 (stageCode 71) i.val % 11 := by decide +kernel

private theorem step_70 : matrixB *ᵥ stageVector 70=stageVector 71 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawB secondRowCode (stageCode 70) (stageCode 71) second_row_binding check_70

private theorem check_71 : ∀ i : Fin 7,
    packedDot 4 (secondRowCode i.val) (stageCode 71) 7 % 11=
      packedDigit 4 (stageCode 72) i.val % 11 := by decide +kernel

private theorem step_71 : matrixB *ᵥ stageVector 71=stageVector 72 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawB secondRowCode (stageCode 71) (stageCode 72) second_row_binding check_71

private theorem check_72 : ∀ i : Fin 7,
    packedDot 4 (firstRowCode i.val) (stageCode 72) 7 % 11=
      packedDigit 4 (stageCode 73) i.val % 11 := by decide +kernel

private theorem step_72 : matrixA *ᵥ stageVector 72=stageVector 73 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawA firstRowCode (stageCode 72) (stageCode 73) first_row_binding check_72

private theorem check_73 : ∀ i : Fin 7,
    packedDot 4 (secondRowCode i.val) (stageCode 73) 7 % 11=
      packedDigit 4 (stageCode 74) i.val % 11 := by decide +kernel

private theorem step_73 : matrixB *ᵥ stageVector 73=stageVector 74 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawB secondRowCode (stageCode 73) (stageCode 74) second_row_binding check_73

private theorem check_74 : ∀ i : Fin 7,
    packedDot 4 (firstRowCode i.val) (stageCode 74) 7 % 11=
      packedDigit 4 (stageCode 75) i.val % 11 := by decide +kernel

private theorem step_74 : matrixA *ᵥ stageVector 74=stageVector 75 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawA firstRowCode (stageCode 74) (stageCode 75) first_row_binding check_74

private theorem check_75 : ∀ i : Fin 7,
    packedDot 4 (secondRowCode i.val) (stageCode 75) 7 % 11=
      packedDigit 4 (stageCode 76) i.val % 11 := by decide +kernel

private theorem step_75 : matrixB *ᵥ stageVector 75=stageVector 76 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawB secondRowCode (stageCode 75) (stageCode 76) second_row_binding check_75

private theorem check_76 : ∀ i : Fin 7,
    packedDot 4 (secondRowCode i.val) (stageCode 76) 7 % 11=
      packedDigit 4 (stageCode 77) i.val % 11 := by decide +kernel

private theorem step_76 : matrixB *ᵥ stageVector 76=stageVector 77 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawB secondRowCode (stageCode 76) (stageCode 77) second_row_binding check_76

private theorem check_77 : ∀ i : Fin 7,
    packedDot 4 (firstRowCode i.val) (stageCode 77) 7 % 11=
      packedDigit 4 (stageCode 78) i.val % 11 := by decide +kernel

private theorem step_77 : matrixA *ᵥ stageVector 77=stageVector 78 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawA firstRowCode (stageCode 77) (stageCode 78) first_row_binding check_77

private theorem check_78 : ∀ i : Fin 7,
    packedDot 4 (secondRowCode i.val) (stageCode 78) 7 % 11=
      packedDigit 4 (stageCode 79) i.val % 11 := by decide +kernel

private theorem step_78 : matrixB *ᵥ stageVector 78=stageVector 79 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawB secondRowCode (stageCode 78) (stageCode 79) second_row_binding check_78

private theorem check_79 : ∀ i : Fin 7,
    packedDot 4 (firstRowCode i.val) (stageCode 79) 7 % 11=
      packedDigit 4 (stageCode 80) i.val % 11 := by decide +kernel

private theorem step_79 : matrixA *ᵥ stageVector 79=stageVector 80 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawA firstRowCode (stageCode 79) (stageCode 80) first_row_binding check_79

private theorem check_80 : ∀ i : Fin 7,
    packedDot 4 (secondRowCode i.val) (stageCode 80) 7 % 11=
      packedDigit 4 (stageCode 81) i.val % 11 := by decide +kernel

private theorem step_80 : matrixB *ᵥ stageVector 80=stageVector 81 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawB secondRowCode (stageCode 80) (stageCode 81) second_row_binding check_80

private theorem check_81 : ∀ i : Fin 7,
    packedDot 4 (secondRowCode i.val) (stageCode 81) 7 % 11=
      packedDigit 4 (stageCode 82) i.val % 11 := by decide +kernel

private theorem step_81 : matrixB *ᵥ stageVector 81=stageVector 82 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawB secondRowCode (stageCode 81) (stageCode 82) second_row_binding check_81

private theorem check_82 : ∀ i : Fin 7,
    packedDot 4 (firstRowCode i.val) (stageCode 82) 7 % 11=
      packedDigit 4 (stageCode 83) i.val % 11 := by decide +kernel

private theorem step_82 : matrixA *ᵥ stageVector 82=stageVector 83 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawA firstRowCode (stageCode 82) (stageCode 83) first_row_binding check_82

private theorem check_83 : ∀ i : Fin 7,
    packedDot 4 (secondRowCode i.val) (stageCode 83) 7 % 11=
      packedDigit 4 (stageCode 84) i.val % 11 := by decide +kernel

private theorem step_83 : matrixB *ᵥ stageVector 83=stageVector 84 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawB secondRowCode (stageCode 83) (stageCode 84) second_row_binding check_83

private theorem check_84 : ∀ i : Fin 7,
    packedDot 4 (firstRowCode i.val) (stageCode 84) 7 % 11=
      packedDigit 4 (stageCode 85) i.val % 11 := by decide +kernel

private theorem step_84 : matrixA *ᵥ stageVector 84=stageVector 85 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawA firstRowCode (stageCode 84) (stageCode 85) first_row_binding check_84

private theorem check_85 : ∀ i : Fin 7,
    packedDot 4 (secondRowCode i.val) (stageCode 85) 7 % 11=
      packedDigit 4 (stageCode 86) i.val % 11 := by decide +kernel

private theorem step_85 : matrixB *ᵥ stageVector 85=stageVector 86 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawB secondRowCode (stageCode 85) (stageCode 86) second_row_binding check_85

private theorem check_86 : ∀ i : Fin 7,
    packedDot 4 (secondRowCode i.val) (stageCode 86) 7 % 11=
      packedDigit 4 (stageCode 87) i.val % 11 := by decide +kernel

private theorem step_86 : matrixB *ᵥ stageVector 86=stageVector 87 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawB secondRowCode (stageCode 86) (stageCode 87) second_row_binding check_86

private theorem check_87 : ∀ i : Fin 7,
    packedDot 4 (firstRowCode i.val) (stageCode 87) 7 % 11=
      packedDigit 4 (stageCode 88) i.val % 11 := by decide +kernel

private theorem step_87 : matrixA *ᵥ stageVector 87=stageVector 88 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawA firstRowCode (stageCode 87) (stageCode 88) first_row_binding check_87

private theorem check_88 : ∀ i : Fin 7,
    packedDot 4 (secondRowCode i.val) (stageCode 88) 7 % 11=
      packedDigit 4 (stageCode 89) i.val % 11 := by decide +kernel

private theorem step_88 : matrixB *ᵥ stageVector 88=stageVector 89 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawB secondRowCode (stageCode 88) (stageCode 89) second_row_binding check_88

private theorem check_89 : ∀ i : Fin 7,
    packedDot 4 (firstRowCode i.val) (stageCode 89) 7 % 11=
      packedDigit 4 (stageCode 90) i.val % 11 := by decide +kernel

private theorem step_89 : matrixA *ᵥ stageVector 89=stageVector 90 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawA firstRowCode (stageCode 89) (stageCode 90) first_row_binding check_89

private theorem check_90 : ∀ i : Fin 7,
    packedDot 4 (secondRowCode i.val) (stageCode 90) 7 % 11=
      packedDigit 4 (stageCode 91) i.val % 11 := by decide +kernel

private theorem step_90 : matrixB *ᵥ stageVector 90=stageVector 91 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawB secondRowCode (stageCode 90) (stageCode 91) second_row_binding check_90

private theorem check_91 : ∀ i : Fin 7,
    packedDot 4 (secondRowCode i.val) (stageCode 91) 7 % 11=
      packedDigit 4 (stageCode 92) i.val % 11 := by decide +kernel

private theorem step_91 : matrixB *ᵥ stageVector 91=stageVector 92 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawB secondRowCode (stageCode 91) (stageCode 92) second_row_binding check_91

private theorem check_92 : ∀ i : Fin 7,
    packedDot 4 (firstRowCode i.val) (stageCode 92) 7 % 11=
      packedDigit 4 (stageCode 93) i.val % 11 := by decide +kernel

private theorem step_92 : matrixA *ᵥ stageVector 92=stageVector 93 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawA firstRowCode (stageCode 92) (stageCode 93) first_row_binding check_92

private theorem check_93 : ∀ i : Fin 7,
    packedDot 4 (secondRowCode i.val) (stageCode 93) 7 % 11=
      packedDigit 4 (stageCode 94) i.val % 11 := by decide +kernel

private theorem step_93 : matrixB *ᵥ stageVector 93=stageVector 94 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawB secondRowCode (stageCode 93) (stageCode 94) second_row_binding check_93

private theorem check_94 : ∀ i : Fin 7,
    packedDot 4 (firstRowCode i.val) (stageCode 94) 7 % 11=
      packedDigit 4 (stageCode 95) i.val % 11 := by decide +kernel

private theorem step_94 : matrixA *ᵥ stageVector 94=stageVector 95 :=
  LinearRepresentationSelectedPrimePeriod.packed_vector_step
    11 7 4 rawA firstRowCode (stageCode 94) (stageCode 95) first_row_binding check_94

private theorem phase_0 (i : Fin 19) :
    matrixB *ᵥ stageVector (5*i.val+0)=stageVector (5*i.val+1) := by
  fin_cases i
  · exact step_0
  · exact step_5
  · exact step_10
  · exact step_15
  · exact step_20
  · exact step_25
  · exact step_30
  · exact step_35
  · exact step_40
  · exact step_45
  · exact step_50
  · exact step_55
  · exact step_60
  · exact step_65
  · exact step_70
  · exact step_75
  · exact step_80
  · exact step_85
  · exact step_90

private theorem phase_1 (i : Fin 19) :
    matrixB *ᵥ stageVector (5*i.val+1)=stageVector (5*i.val+2) := by
  fin_cases i
  · exact step_1
  · exact step_6
  · exact step_11
  · exact step_16
  · exact step_21
  · exact step_26
  · exact step_31
  · exact step_36
  · exact step_41
  · exact step_46
  · exact step_51
  · exact step_56
  · exact step_61
  · exact step_66
  · exact step_71
  · exact step_76
  · exact step_81
  · exact step_86
  · exact step_91

private theorem phase_2 (i : Fin 19) :
    matrixA *ᵥ stageVector (5*i.val+2)=stageVector (5*i.val+3) := by
  fin_cases i
  · exact step_2
  · exact step_7
  · exact step_12
  · exact step_17
  · exact step_22
  · exact step_27
  · exact step_32
  · exact step_37
  · exact step_42
  · exact step_47
  · exact step_52
  · exact step_57
  · exact step_62
  · exact step_67
  · exact step_72
  · exact step_77
  · exact step_82
  · exact step_87
  · exact step_92

private theorem phase_3 (i : Fin 19) :
    matrixB *ᵥ stageVector (5*i.val+3)=stageVector (5*i.val+4) := by
  fin_cases i
  · exact step_3
  · exact step_8
  · exact step_13
  · exact step_18
  · exact step_23
  · exact step_28
  · exact step_33
  · exact step_38
  · exact step_43
  · exact step_48
  · exact step_53
  · exact step_58
  · exact step_63
  · exact step_68
  · exact step_73
  · exact step_78
  · exact step_83
  · exact step_88
  · exact step_93

private theorem phase_4 (i : Fin 19) :
    matrixA *ᵥ stageVector (5*i.val+4)=stageVector (5*i.val+5) := by
  fin_cases i
  · exact step_4
  · exact step_9
  · exact step_14
  · exact step_19
  · exact step_24
  · exact step_29
  · exact step_34
  · exact step_39
  · exact step_44
  · exact step_49
  · exact step_54
  · exact step_59
  · exact step_64
  · exact step_69
  · exact step_74
  · exact step_79
  · exact step_84
  · exact step_89
  · exact step_94

theorem word_step (i : Fin 19) : wordEnd (vectors i.castSucc)=vectors i.succ := by
  rw [wordEnd_apply]
  change matrixA *ᵥ (matrixB *ᵥ (matrixA *ᵥ (matrixB *ᵥ
    (matrixB *ᵥ stageVector (5*i.val+0)))))=stageVector (5*(i.val+1))
  rw [phase_0,phase_1,phase_2,phase_3,phase_4]
  exact congrArg stageVector (by omega)

set_option maxRecDepth 4096 in
theorem selected_return : (wordEnd^19) (vectors 0)=vectors 0 := by
  have hp := LinearMapSelectedKrylovPeriod.pow_apply_eq_vector wordEnd 19 vectors
    word_step (Fin.last 19)
  have he : vectors (Fin.last 19)=vectors 0 := by
    funext j
    fin_cases j <;> decide +kernel
  exact hp.trans he

theorem selected_moved : wordEnd (vectors 0)≠vectors 0 := by
  intro he
  have hn : vectors 1 (1 : Fin 7)≠vectors 0 (1 : Fin 7) := by decide +kernel
  exact hn (congrArg (fun v : V => v (1 : Fin 7)) ((word_step 0).symm.trans he))

set_option maxRecDepth 4096 in
theorem nineteen_dvd_card [Finite Model] : 19∣Nat.card Model := by
  apply LinearRepresentationSelectedPrimePeriod.prime_dvd_card ρ selectedWord 19
    (by decide) (vectors 0)
  · rw [word_binding]
    exact selected_return
  · rw [word_binding]
    exact selected_moved

end SymmetricSubgroupAsymptotics.CFSGJankoOneSelectedPrimeNineteen
