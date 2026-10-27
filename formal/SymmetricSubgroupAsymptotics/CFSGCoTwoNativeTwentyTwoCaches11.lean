import SymmetricSubgroupAsymptotics.MatrixKroneckerProductReflection
import Mathlib.Tactic.FinCases

/-! Fixed Co2 binary22 shared caches. Every digit and pack binding is kernel checked. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoCaches11
open MatrixKroneckerProductReflection MatrixKroneckerDotReflection
open MatrixNaturalRowDotReflection SmallNaturalMatrixProductReflection

def R10p03_lowColumnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 3549344
  | 1 => 408320
  | 2 => 1207264
  | 3 => 2509312
  | 4 => 352865
  | 5 => 3344384
  | 6 => 3268608
  | 7 => 2805984
  | 8 => 2385920
  | 9 => 3434627
  | 10 => 2277376
  | 11 => 2533376
  | 12 => 3547584
  | 13 => 3620968
  | 14 => 3641796
  | 15 => 1465216
  | 16 => 1220608
  | 17 => 3491984
  | 18 => 3152544
  | 19 => 3239936
  | 20 => 2191360
  | 21 => 472064
  | _ => 0

def R10p03_rowCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 35184373137408
  | 1 => 35184372088832
  | 2 => 1180591620717411303424
  | 3 => 36893488147419103232
  | 4 => 38685626227668133590597632
  | 5 => 1237940076178868456679015425
  | 6 => 1218638030403798041600
  | 7 => 1276664626189488806401410049
  | 8 => 38960676405179179861024
  | 9 => 1237977818217243232061916192
  | 10 => 40564819207303340847894502572032
  | 11 => 1276663444480976446587700257
  | 12 => 41873321867787511282171809628192
  | 13 => 41872085097715711019403736777761
  | 14 => 1307303404927415751750871712768
  | 15 => 1210106448390078945296384
  | 16 => 41872122575632415195187507101696
  | 17 => 40564820455226767510581595374625
  | 18 => 40564857931927174474435595894817
  | 19 => 34359738368
  | 20 => 40891954846034760346514752513
  | 21 => 1308541308369549840087678746625
  | _ => 0

def R10p03_columnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 1210106412362346005561377
  | 1 => 38047571835817590784
  | 2 => 1247923390634989552926752
  | 3 => 1154047438874509313
  | 4 => 40564820454009245248119350788096
  | 5 => 1125899941445665
  | 6 => 1134978662433
  | 7 => 1247885343133523554337793
  | 8 => 1127033778241537
  | 9 => 41832469808712162997142395322401
  | 10 => 35434528769
  | 11 => 1127000493293569
  | 12 => 38996416972921504825377
  | 13 => 1239186744036857895629914145
  | 14 => 39614120253549175804244557857
  | 15 => 1218639191488077004832
  | 16 => 1100586418208
  | 17 => 38686806820414785302069281
  | 18 => 1210107565317935471788065
  | 19 => 36318277009441
  | 20 => 36318277009409
  | 21 => 36065080937316352
  | _ => 0

def R10p03_digit (i j : Fin 22) : ℕ := packedDigit 1 (R10p03_lowColumnCode j) i.val

private theorem R10p03_bound_00 : ∀ j : Fin 22,R10p03_digit 0 j<2 := by decide +kernel

private theorem R10p03_bound_01 : ∀ j : Fin 22,R10p03_digit 1 j<2 := by decide +kernel

private theorem R10p03_bound_02 : ∀ j : Fin 22,R10p03_digit 2 j<2 := by decide +kernel

private theorem R10p03_bound_03 : ∀ j : Fin 22,R10p03_digit 3 j<2 := by decide +kernel

private theorem R10p03_bound_04 : ∀ j : Fin 22,R10p03_digit 4 j<2 := by decide +kernel

private theorem R10p03_bound_05 : ∀ j : Fin 22,R10p03_digit 5 j<2 := by decide +kernel

private theorem R10p03_bound_06 : ∀ j : Fin 22,R10p03_digit 6 j<2 := by decide +kernel

private theorem R10p03_bound_07 : ∀ j : Fin 22,R10p03_digit 7 j<2 := by decide +kernel

private theorem R10p03_bound_08 : ∀ j : Fin 22,R10p03_digit 8 j<2 := by decide +kernel

private theorem R10p03_bound_09 : ∀ j : Fin 22,R10p03_digit 9 j<2 := by decide +kernel

private theorem R10p03_bound_10 : ∀ j : Fin 22,R10p03_digit 10 j<2 := by decide +kernel

private theorem R10p03_bound_11 : ∀ j : Fin 22,R10p03_digit 11 j<2 := by decide +kernel

private theorem R10p03_bound_12 : ∀ j : Fin 22,R10p03_digit 12 j<2 := by decide +kernel

private theorem R10p03_bound_13 : ∀ j : Fin 22,R10p03_digit 13 j<2 := by decide +kernel

private theorem R10p03_bound_14 : ∀ j : Fin 22,R10p03_digit 14 j<2 := by decide +kernel

private theorem R10p03_bound_15 : ∀ j : Fin 22,R10p03_digit 15 j<2 := by decide +kernel

private theorem R10p03_bound_16 : ∀ j : Fin 22,R10p03_digit 16 j<2 := by decide +kernel

private theorem R10p03_bound_17 : ∀ j : Fin 22,R10p03_digit 17 j<2 := by decide +kernel

private theorem R10p03_bound_18 : ∀ j : Fin 22,R10p03_digit 18 j<2 := by decide +kernel

private theorem R10p03_bound_19 : ∀ j : Fin 22,R10p03_digit 19 j<2 := by decide +kernel

private theorem R10p03_bound_20 : ∀ j : Fin 22,R10p03_digit 20 j<2 := by decide +kernel

private theorem R10p03_bound_21 : ∀ j : Fin 22,R10p03_digit 21 j<2 := by decide +kernel

theorem R10p03_bound : ∀ i j : Fin 22,R10p03_digit i j<2 := by
  intro i j
  fin_cases i
  · exact R10p03_bound_00 j
  · exact R10p03_bound_01 j
  · exact R10p03_bound_02 j
  · exact R10p03_bound_03 j
  · exact R10p03_bound_04 j
  · exact R10p03_bound_05 j
  · exact R10p03_bound_06 j
  · exact R10p03_bound_07 j
  · exact R10p03_bound_08 j
  · exact R10p03_bound_09 j
  · exact R10p03_bound_10 j
  · exact R10p03_bound_11 j
  · exact R10p03_bound_12 j
  · exact R10p03_bound_13 j
  · exact R10p03_bound_14 j
  · exact R10p03_bound_15 j
  · exact R10p03_bound_16 j
  · exact R10p03_bound_17 j
  · exact R10p03_bound_18 j
  · exact R10p03_bound_19 j
  · exact R10p03_bound_20 j
  · exact R10p03_bound_21 j

private theorem R10p03_row_00 : pack 32 (R10p03_digit 0)=R10p03_rowCode 0 := by decide +kernel

private theorem R10p03_row_01 : pack 32 (R10p03_digit 1)=R10p03_rowCode 1 := by decide +kernel

private theorem R10p03_row_02 : pack 32 (R10p03_digit 2)=R10p03_rowCode 2 := by decide +kernel

private theorem R10p03_row_03 : pack 32 (R10p03_digit 3)=R10p03_rowCode 3 := by decide +kernel

private theorem R10p03_row_04 : pack 32 (R10p03_digit 4)=R10p03_rowCode 4 := by decide +kernel

private theorem R10p03_row_05 : pack 32 (R10p03_digit 5)=R10p03_rowCode 5 := by decide +kernel

private theorem R10p03_row_06 : pack 32 (R10p03_digit 6)=R10p03_rowCode 6 := by decide +kernel

private theorem R10p03_row_07 : pack 32 (R10p03_digit 7)=R10p03_rowCode 7 := by decide +kernel

private theorem R10p03_row_08 : pack 32 (R10p03_digit 8)=R10p03_rowCode 8 := by decide +kernel

private theorem R10p03_row_09 : pack 32 (R10p03_digit 9)=R10p03_rowCode 9 := by decide +kernel

private theorem R10p03_row_10 : pack 32 (R10p03_digit 10)=R10p03_rowCode 10 := by decide +kernel

private theorem R10p03_row_11 : pack 32 (R10p03_digit 11)=R10p03_rowCode 11 := by decide +kernel

private theorem R10p03_row_12 : pack 32 (R10p03_digit 12)=R10p03_rowCode 12 := by decide +kernel

private theorem R10p03_row_13 : pack 32 (R10p03_digit 13)=R10p03_rowCode 13 := by decide +kernel

private theorem R10p03_row_14 : pack 32 (R10p03_digit 14)=R10p03_rowCode 14 := by decide +kernel

private theorem R10p03_row_15 : pack 32 (R10p03_digit 15)=R10p03_rowCode 15 := by decide +kernel

private theorem R10p03_row_16 : pack 32 (R10p03_digit 16)=R10p03_rowCode 16 := by decide +kernel

private theorem R10p03_row_17 : pack 32 (R10p03_digit 17)=R10p03_rowCode 17 := by decide +kernel

private theorem R10p03_row_18 : pack 32 (R10p03_digit 18)=R10p03_rowCode 18 := by decide +kernel

private theorem R10p03_row_19 : pack 32 (R10p03_digit 19)=R10p03_rowCode 19 := by decide +kernel

private theorem R10p03_row_20 : pack 32 (R10p03_digit 20)=R10p03_rowCode 20 := by decide +kernel

private theorem R10p03_row_21 : pack 32 (R10p03_digit 21)=R10p03_rowCode 21 := by decide +kernel

theorem R10p03_row_binding : ∀ i : Fin 22,pack 32 (R10p03_digit i)=R10p03_rowCode i := by
  intro i
  fin_cases i
  · exact R10p03_row_00
  · exact R10p03_row_01
  · exact R10p03_row_02
  · exact R10p03_row_03
  · exact R10p03_row_04
  · exact R10p03_row_05
  · exact R10p03_row_06
  · exact R10p03_row_07
  · exact R10p03_row_08
  · exact R10p03_row_09
  · exact R10p03_row_10
  · exact R10p03_row_11
  · exact R10p03_row_12
  · exact R10p03_row_13
  · exact R10p03_row_14
  · exact R10p03_row_15
  · exact R10p03_row_16
  · exact R10p03_row_17
  · exact R10p03_row_18
  · exact R10p03_row_19
  · exact R10p03_row_20
  · exact R10p03_row_21

private theorem R10p03_column_00 : reversePack 32 (fun j : Fin 22 => R10p03_digit j 0)=R10p03_columnCode 0 := by decide +kernel

private theorem R10p03_column_01 : reversePack 32 (fun j : Fin 22 => R10p03_digit j 1)=R10p03_columnCode 1 := by decide +kernel

private theorem R10p03_column_02 : reversePack 32 (fun j : Fin 22 => R10p03_digit j 2)=R10p03_columnCode 2 := by decide +kernel

private theorem R10p03_column_03 : reversePack 32 (fun j : Fin 22 => R10p03_digit j 3)=R10p03_columnCode 3 := by decide +kernel

private theorem R10p03_column_04 : reversePack 32 (fun j : Fin 22 => R10p03_digit j 4)=R10p03_columnCode 4 := by decide +kernel

private theorem R10p03_column_05 : reversePack 32 (fun j : Fin 22 => R10p03_digit j 5)=R10p03_columnCode 5 := by decide +kernel

private theorem R10p03_column_06 : reversePack 32 (fun j : Fin 22 => R10p03_digit j 6)=R10p03_columnCode 6 := by decide +kernel

private theorem R10p03_column_07 : reversePack 32 (fun j : Fin 22 => R10p03_digit j 7)=R10p03_columnCode 7 := by decide +kernel

private theorem R10p03_column_08 : reversePack 32 (fun j : Fin 22 => R10p03_digit j 8)=R10p03_columnCode 8 := by decide +kernel

private theorem R10p03_column_09 : reversePack 32 (fun j : Fin 22 => R10p03_digit j 9)=R10p03_columnCode 9 := by decide +kernel

private theorem R10p03_column_10 : reversePack 32 (fun j : Fin 22 => R10p03_digit j 10)=R10p03_columnCode 10 := by decide +kernel

private theorem R10p03_column_11 : reversePack 32 (fun j : Fin 22 => R10p03_digit j 11)=R10p03_columnCode 11 := by decide +kernel

private theorem R10p03_column_12 : reversePack 32 (fun j : Fin 22 => R10p03_digit j 12)=R10p03_columnCode 12 := by decide +kernel

private theorem R10p03_column_13 : reversePack 32 (fun j : Fin 22 => R10p03_digit j 13)=R10p03_columnCode 13 := by decide +kernel

private theorem R10p03_column_14 : reversePack 32 (fun j : Fin 22 => R10p03_digit j 14)=R10p03_columnCode 14 := by decide +kernel

private theorem R10p03_column_15 : reversePack 32 (fun j : Fin 22 => R10p03_digit j 15)=R10p03_columnCode 15 := by decide +kernel

private theorem R10p03_column_16 : reversePack 32 (fun j : Fin 22 => R10p03_digit j 16)=R10p03_columnCode 16 := by decide +kernel

private theorem R10p03_column_17 : reversePack 32 (fun j : Fin 22 => R10p03_digit j 17)=R10p03_columnCode 17 := by decide +kernel

private theorem R10p03_column_18 : reversePack 32 (fun j : Fin 22 => R10p03_digit j 18)=R10p03_columnCode 18 := by decide +kernel

private theorem R10p03_column_19 : reversePack 32 (fun j : Fin 22 => R10p03_digit j 19)=R10p03_columnCode 19 := by decide +kernel

private theorem R10p03_column_20 : reversePack 32 (fun j : Fin 22 => R10p03_digit j 20)=R10p03_columnCode 20 := by decide +kernel

private theorem R10p03_column_21 : reversePack 32 (fun j : Fin 22 => R10p03_digit j 21)=R10p03_columnCode 21 := by decide +kernel

theorem R10p03_column_binding : ∀ i : Fin 22,reversePack 32 (fun j : Fin 22 => R10p03_digit j i)=R10p03_columnCode i := by
  intro i
  fin_cases i
  · exact R10p03_column_00
  · exact R10p03_column_01
  · exact R10p03_column_02
  · exact R10p03_column_03
  · exact R10p03_column_04
  · exact R10p03_column_05
  · exact R10p03_column_06
  · exact R10p03_column_07
  · exact R10p03_column_08
  · exact R10p03_column_09
  · exact R10p03_column_10
  · exact R10p03_column_11
  · exact R10p03_column_12
  · exact R10p03_column_13
  · exact R10p03_column_14
  · exact R10p03_column_15
  · exact R10p03_column_16
  · exact R10p03_column_17
  · exact R10p03_column_18
  · exact R10p03_column_19
  · exact R10p03_column_20
  · exact R10p03_column_21

def R10p03_data : PackedData 22 2 32 where
  raw := R10p03_digit
  digit_lt := R10p03_bound
  rowCode := R10p03_rowCode
  columnCode := R10p03_columnCode
  row_binding := R10p03_row_binding
  column_binding := R10p03_column_binding

def R10p04_lowColumnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 194119
  | 1 => 3335655
  | 2 => 473600
  | 3 => 3349472
  | 4 => 3766996
  | 5 => 2799011
  | 6 => 915637
  | 7 => 2805984
  | 8 => 4052387
  | 9 => 3434627
  | 10 => 2277376
  | 11 => 2533376
  | 12 => 3547584
  | 13 => 327328
  | 14 => 3641796
  | 15 => 3416624
  | 16 => 2170568
  | 17 => 3491984
  | 18 => 3152544
  | 19 => 1247664
  | 20 => 2191360
  | 21 => 472064
  | _ => 0

def R10p04_rowCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 36284991012897
  | 1 => 36283917271073
  | 2 => 1180591620718486093857
  | 3 => 1208925819614629174706176
  | 4 => 39652804662291699888599072768
  | 5 => 40852059112242901311230607392
  | 6 => 1210107564156885553676321
  | 7 => 40891917067102898523225489440
  | 8 => 39614082438876712118335340576
  | 9 => 1239186780930346008655725569
  | 10 => 40564820416266053951770641563681
  | 11 => 40891915885394383964321383424
  | 12 => 41833708957714160354295089759233
  | 13 => 41832469845348584585982892835873
  | 14 => 1267689285891351719996937994273
  | 15 => 1217522264696734875681
  | 16 => 41872123784521341322768740811776
  | 17 => 40604433289742254713644611830817
  | 18 => 40564857931927174474436668556288
  | 19 => 1134979710976
  | 20 => 40890745883321658668326354976
  | 21 => 1268928473780275660728751390752
  | _ => 0

def R10p04_columnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 41872083926568823267766083518464
  | 1 => 41872085136710975034571109695521
  | 2 => 1154083688432041984
  | 3 => 1247923390669040087203873
  | 4 => 39652805844037404327726285857
  | 5 => 41832471017674911037967188362241
  | 6 => 40604473184293113082390708782080
  | 7 => 1247885343133523554337793
  | 8 => 41832471017674911036902069011489
  | 9 => 41832469808712162997142395322401
  | 10 => 35434528769
  | 11 => 1127000493293569
  | 12 => 38996416972921504825377
  | 13 => 1210107601347867435892736
  | 14 => 39614120253549175804244557857
  | 15 => 39894553200205366883811361
  | 16 => 1237978999998975335410434049
  | 17 => 38686806820414785302069281
  | 18 => 1210107565317935471788065
  | 19 => 39895769533517527537156128
  | 20 => 36318277009409
  | 21 => 36065080937316352
  | _ => 0

def R10p04_digit (i j : Fin 22) : ℕ := packedDigit 1 (R10p04_lowColumnCode j) i.val

private theorem R10p04_bound_00 : ∀ j : Fin 22,R10p04_digit 0 j<2 := by decide +kernel

private theorem R10p04_bound_01 : ∀ j : Fin 22,R10p04_digit 1 j<2 := by decide +kernel

private theorem R10p04_bound_02 : ∀ j : Fin 22,R10p04_digit 2 j<2 := by decide +kernel

private theorem R10p04_bound_03 : ∀ j : Fin 22,R10p04_digit 3 j<2 := by decide +kernel

private theorem R10p04_bound_04 : ∀ j : Fin 22,R10p04_digit 4 j<2 := by decide +kernel

private theorem R10p04_bound_05 : ∀ j : Fin 22,R10p04_digit 5 j<2 := by decide +kernel

private theorem R10p04_bound_06 : ∀ j : Fin 22,R10p04_digit 6 j<2 := by decide +kernel

private theorem R10p04_bound_07 : ∀ j : Fin 22,R10p04_digit 7 j<2 := by decide +kernel

private theorem R10p04_bound_08 : ∀ j : Fin 22,R10p04_digit 8 j<2 := by decide +kernel

private theorem R10p04_bound_09 : ∀ j : Fin 22,R10p04_digit 9 j<2 := by decide +kernel

private theorem R10p04_bound_10 : ∀ j : Fin 22,R10p04_digit 10 j<2 := by decide +kernel

private theorem R10p04_bound_11 : ∀ j : Fin 22,R10p04_digit 11 j<2 := by decide +kernel

private theorem R10p04_bound_12 : ∀ j : Fin 22,R10p04_digit 12 j<2 := by decide +kernel

private theorem R10p04_bound_13 : ∀ j : Fin 22,R10p04_digit 13 j<2 := by decide +kernel

private theorem R10p04_bound_14 : ∀ j : Fin 22,R10p04_digit 14 j<2 := by decide +kernel

private theorem R10p04_bound_15 : ∀ j : Fin 22,R10p04_digit 15 j<2 := by decide +kernel

private theorem R10p04_bound_16 : ∀ j : Fin 22,R10p04_digit 16 j<2 := by decide +kernel

private theorem R10p04_bound_17 : ∀ j : Fin 22,R10p04_digit 17 j<2 := by decide +kernel

private theorem R10p04_bound_18 : ∀ j : Fin 22,R10p04_digit 18 j<2 := by decide +kernel

private theorem R10p04_bound_19 : ∀ j : Fin 22,R10p04_digit 19 j<2 := by decide +kernel

private theorem R10p04_bound_20 : ∀ j : Fin 22,R10p04_digit 20 j<2 := by decide +kernel

private theorem R10p04_bound_21 : ∀ j : Fin 22,R10p04_digit 21 j<2 := by decide +kernel

theorem R10p04_bound : ∀ i j : Fin 22,R10p04_digit i j<2 := by
  intro i j
  fin_cases i
  · exact R10p04_bound_00 j
  · exact R10p04_bound_01 j
  · exact R10p04_bound_02 j
  · exact R10p04_bound_03 j
  · exact R10p04_bound_04 j
  · exact R10p04_bound_05 j
  · exact R10p04_bound_06 j
  · exact R10p04_bound_07 j
  · exact R10p04_bound_08 j
  · exact R10p04_bound_09 j
  · exact R10p04_bound_10 j
  · exact R10p04_bound_11 j
  · exact R10p04_bound_12 j
  · exact R10p04_bound_13 j
  · exact R10p04_bound_14 j
  · exact R10p04_bound_15 j
  · exact R10p04_bound_16 j
  · exact R10p04_bound_17 j
  · exact R10p04_bound_18 j
  · exact R10p04_bound_19 j
  · exact R10p04_bound_20 j
  · exact R10p04_bound_21 j

private theorem R10p04_row_00 : pack 32 (R10p04_digit 0)=R10p04_rowCode 0 := by decide +kernel

private theorem R10p04_row_01 : pack 32 (R10p04_digit 1)=R10p04_rowCode 1 := by decide +kernel

private theorem R10p04_row_02 : pack 32 (R10p04_digit 2)=R10p04_rowCode 2 := by decide +kernel

private theorem R10p04_row_03 : pack 32 (R10p04_digit 3)=R10p04_rowCode 3 := by decide +kernel

private theorem R10p04_row_04 : pack 32 (R10p04_digit 4)=R10p04_rowCode 4 := by decide +kernel

private theorem R10p04_row_05 : pack 32 (R10p04_digit 5)=R10p04_rowCode 5 := by decide +kernel

private theorem R10p04_row_06 : pack 32 (R10p04_digit 6)=R10p04_rowCode 6 := by decide +kernel

private theorem R10p04_row_07 : pack 32 (R10p04_digit 7)=R10p04_rowCode 7 := by decide +kernel

private theorem R10p04_row_08 : pack 32 (R10p04_digit 8)=R10p04_rowCode 8 := by decide +kernel

private theorem R10p04_row_09 : pack 32 (R10p04_digit 9)=R10p04_rowCode 9 := by decide +kernel

private theorem R10p04_row_10 : pack 32 (R10p04_digit 10)=R10p04_rowCode 10 := by decide +kernel

private theorem R10p04_row_11 : pack 32 (R10p04_digit 11)=R10p04_rowCode 11 := by decide +kernel

private theorem R10p04_row_12 : pack 32 (R10p04_digit 12)=R10p04_rowCode 12 := by decide +kernel

private theorem R10p04_row_13 : pack 32 (R10p04_digit 13)=R10p04_rowCode 13 := by decide +kernel

private theorem R10p04_row_14 : pack 32 (R10p04_digit 14)=R10p04_rowCode 14 := by decide +kernel

private theorem R10p04_row_15 : pack 32 (R10p04_digit 15)=R10p04_rowCode 15 := by decide +kernel

private theorem R10p04_row_16 : pack 32 (R10p04_digit 16)=R10p04_rowCode 16 := by decide +kernel

private theorem R10p04_row_17 : pack 32 (R10p04_digit 17)=R10p04_rowCode 17 := by decide +kernel

private theorem R10p04_row_18 : pack 32 (R10p04_digit 18)=R10p04_rowCode 18 := by decide +kernel

private theorem R10p04_row_19 : pack 32 (R10p04_digit 19)=R10p04_rowCode 19 := by decide +kernel

private theorem R10p04_row_20 : pack 32 (R10p04_digit 20)=R10p04_rowCode 20 := by decide +kernel

private theorem R10p04_row_21 : pack 32 (R10p04_digit 21)=R10p04_rowCode 21 := by decide +kernel

theorem R10p04_row_binding : ∀ i : Fin 22,pack 32 (R10p04_digit i)=R10p04_rowCode i := by
  intro i
  fin_cases i
  · exact R10p04_row_00
  · exact R10p04_row_01
  · exact R10p04_row_02
  · exact R10p04_row_03
  · exact R10p04_row_04
  · exact R10p04_row_05
  · exact R10p04_row_06
  · exact R10p04_row_07
  · exact R10p04_row_08
  · exact R10p04_row_09
  · exact R10p04_row_10
  · exact R10p04_row_11
  · exact R10p04_row_12
  · exact R10p04_row_13
  · exact R10p04_row_14
  · exact R10p04_row_15
  · exact R10p04_row_16
  · exact R10p04_row_17
  · exact R10p04_row_18
  · exact R10p04_row_19
  · exact R10p04_row_20
  · exact R10p04_row_21

private theorem R10p04_column_00 : reversePack 32 (fun j : Fin 22 => R10p04_digit j 0)=R10p04_columnCode 0 := by decide +kernel

private theorem R10p04_column_01 : reversePack 32 (fun j : Fin 22 => R10p04_digit j 1)=R10p04_columnCode 1 := by decide +kernel

private theorem R10p04_column_02 : reversePack 32 (fun j : Fin 22 => R10p04_digit j 2)=R10p04_columnCode 2 := by decide +kernel

private theorem R10p04_column_03 : reversePack 32 (fun j : Fin 22 => R10p04_digit j 3)=R10p04_columnCode 3 := by decide +kernel

private theorem R10p04_column_04 : reversePack 32 (fun j : Fin 22 => R10p04_digit j 4)=R10p04_columnCode 4 := by decide +kernel

private theorem R10p04_column_05 : reversePack 32 (fun j : Fin 22 => R10p04_digit j 5)=R10p04_columnCode 5 := by decide +kernel

private theorem R10p04_column_06 : reversePack 32 (fun j : Fin 22 => R10p04_digit j 6)=R10p04_columnCode 6 := by decide +kernel

private theorem R10p04_column_07 : reversePack 32 (fun j : Fin 22 => R10p04_digit j 7)=R10p04_columnCode 7 := by decide +kernel

private theorem R10p04_column_08 : reversePack 32 (fun j : Fin 22 => R10p04_digit j 8)=R10p04_columnCode 8 := by decide +kernel

private theorem R10p04_column_09 : reversePack 32 (fun j : Fin 22 => R10p04_digit j 9)=R10p04_columnCode 9 := by decide +kernel

private theorem R10p04_column_10 : reversePack 32 (fun j : Fin 22 => R10p04_digit j 10)=R10p04_columnCode 10 := by decide +kernel

private theorem R10p04_column_11 : reversePack 32 (fun j : Fin 22 => R10p04_digit j 11)=R10p04_columnCode 11 := by decide +kernel

private theorem R10p04_column_12 : reversePack 32 (fun j : Fin 22 => R10p04_digit j 12)=R10p04_columnCode 12 := by decide +kernel

private theorem R10p04_column_13 : reversePack 32 (fun j : Fin 22 => R10p04_digit j 13)=R10p04_columnCode 13 := by decide +kernel

private theorem R10p04_column_14 : reversePack 32 (fun j : Fin 22 => R10p04_digit j 14)=R10p04_columnCode 14 := by decide +kernel

private theorem R10p04_column_15 : reversePack 32 (fun j : Fin 22 => R10p04_digit j 15)=R10p04_columnCode 15 := by decide +kernel

private theorem R10p04_column_16 : reversePack 32 (fun j : Fin 22 => R10p04_digit j 16)=R10p04_columnCode 16 := by decide +kernel

private theorem R10p04_column_17 : reversePack 32 (fun j : Fin 22 => R10p04_digit j 17)=R10p04_columnCode 17 := by decide +kernel

private theorem R10p04_column_18 : reversePack 32 (fun j : Fin 22 => R10p04_digit j 18)=R10p04_columnCode 18 := by decide +kernel

private theorem R10p04_column_19 : reversePack 32 (fun j : Fin 22 => R10p04_digit j 19)=R10p04_columnCode 19 := by decide +kernel

private theorem R10p04_column_20 : reversePack 32 (fun j : Fin 22 => R10p04_digit j 20)=R10p04_columnCode 20 := by decide +kernel

private theorem R10p04_column_21 : reversePack 32 (fun j : Fin 22 => R10p04_digit j 21)=R10p04_columnCode 21 := by decide +kernel

theorem R10p04_column_binding : ∀ i : Fin 22,reversePack 32 (fun j : Fin 22 => R10p04_digit j i)=R10p04_columnCode i := by
  intro i
  fin_cases i
  · exact R10p04_column_00
  · exact R10p04_column_01
  · exact R10p04_column_02
  · exact R10p04_column_03
  · exact R10p04_column_04
  · exact R10p04_column_05
  · exact R10p04_column_06
  · exact R10p04_column_07
  · exact R10p04_column_08
  · exact R10p04_column_09
  · exact R10p04_column_10
  · exact R10p04_column_11
  · exact R10p04_column_12
  · exact R10p04_column_13
  · exact R10p04_column_14
  · exact R10p04_column_15
  · exact R10p04_column_16
  · exact R10p04_column_17
  · exact R10p04_column_18
  · exact R10p04_column_19
  · exact R10p04_column_20
  · exact R10p04_column_21

def R10p04_data : PackedData 22 2 32 where
  raw := R10p04_digit
  digit_lt := R10p04_bound
  rowCode := R10p04_rowCode
  columnCode := R10p04_columnCode
  row_binding := R10p04_row_binding
  column_binding := R10p04_column_binding

def R10p05_lowColumnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 1455976
  | 1 => 1309487
  | 2 => 629739
  | 3 => 2658253
  | 4 => 1716703
  | 5 => 3560173
  | 6 => 3944709
  | 7 => 2353295
  | 8 => 2714331
  | 9 => 3414958
  | 10 => 2627805
  | 11 => 3691295
  | 12 => 3545182
  | 13 => 1683181
  | 14 => 2937291
  | 15 => 3219854
  | 16 => 3307952
  | 17 => 4190157
  | 18 => 3070995
  | 19 => 3282808
  | 20 => 472064
  | 21 => 2170568
  | _ => 0

def R10p05_rowCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 1276626883035313105225679904
  | 1 => 1237978999997850569342452768
  | 2 => 38723443243130659544268832
  | 3 => 40604472013184307769166668006433
  | 4 => 40853230223427241001891135488
  | 5 => 39615290219845306757771428897
  | 6 => 40604471975405339842193755505665
  | 7 => 40564859140851806264697444926464
  | 8 => 39654014768738999216576168993
  | 9 => 40604471974223630238053220516897
  | 10 => 41873360514491108954743886610433
  | 11 => 40566097041932721082802343281696
  | 12 => 41873323038935589145196475974689
  | 13 => 1267690532596102036498995478561
  | 14 => 1277835771960313685999616032
  | 15 => 1276626882998157307679900704
  | 16 => 41832508530973623269763248555040
  | 17 => 1308542516077847154870140796961
  | 18 => 1268927227075487027312690462721
  | 19 => 1276626883035313070832387072
  | 20 => 39654013626193788151224336417
  | 21 => 40605711162112519275924395425792
  | _ => 0

def R10p05_columnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 1239186782119332594165252128
  | 1 => 41873323037791854984963336175648
  | 2 => 41833708995494246298707264799744
  | 3 => 40605671267597365444990772184065
  | 4 => 41873360553450632474702344356896
  | 5 => 40605672476486254451993261146145
  | 6 => 40604433288597366541122577400865
  | 7 => 41873321830008580546215174733825
  | 8 => 41833746472157760830012687123457
  | 9 => 1308503831669105756651265228833
  | 10 => 40605709953185510709858616214529
  | 11 => 41873360514492261911467225252897
  | 12 => 1308541344929807642743406624801
  | 13 => 40605672476486291572572072969248
  | 14 => 41833707786567272636707902620673
  | 15 => 1308502622742132060532749893665
  | 16 => 39895769533553845747056673
  | 17 => 40605671267597365446124678186017
  | 18 => 41832508493157835107441528833025
  | 19 => 1277872408346999628244189217
  | 20 => 36065080937316352
  | 21 => 1237978999998975335410434049
  | _ => 0

def R10p05_digit (i j : Fin 22) : ℕ := packedDigit 1 (R10p05_lowColumnCode j) i.val

private theorem R10p05_bound_00 : ∀ j : Fin 22,R10p05_digit 0 j<2 := by decide +kernel

private theorem R10p05_bound_01 : ∀ j : Fin 22,R10p05_digit 1 j<2 := by decide +kernel

private theorem R10p05_bound_02 : ∀ j : Fin 22,R10p05_digit 2 j<2 := by decide +kernel

private theorem R10p05_bound_03 : ∀ j : Fin 22,R10p05_digit 3 j<2 := by decide +kernel

private theorem R10p05_bound_04 : ∀ j : Fin 22,R10p05_digit 4 j<2 := by decide +kernel

private theorem R10p05_bound_05 : ∀ j : Fin 22,R10p05_digit 5 j<2 := by decide +kernel

private theorem R10p05_bound_06 : ∀ j : Fin 22,R10p05_digit 6 j<2 := by decide +kernel

private theorem R10p05_bound_07 : ∀ j : Fin 22,R10p05_digit 7 j<2 := by decide +kernel

private theorem R10p05_bound_08 : ∀ j : Fin 22,R10p05_digit 8 j<2 := by decide +kernel

private theorem R10p05_bound_09 : ∀ j : Fin 22,R10p05_digit 9 j<2 := by decide +kernel

private theorem R10p05_bound_10 : ∀ j : Fin 22,R10p05_digit 10 j<2 := by decide +kernel

private theorem R10p05_bound_11 : ∀ j : Fin 22,R10p05_digit 11 j<2 := by decide +kernel

private theorem R10p05_bound_12 : ∀ j : Fin 22,R10p05_digit 12 j<2 := by decide +kernel

private theorem R10p05_bound_13 : ∀ j : Fin 22,R10p05_digit 13 j<2 := by decide +kernel

private theorem R10p05_bound_14 : ∀ j : Fin 22,R10p05_digit 14 j<2 := by decide +kernel

private theorem R10p05_bound_15 : ∀ j : Fin 22,R10p05_digit 15 j<2 := by decide +kernel

private theorem R10p05_bound_16 : ∀ j : Fin 22,R10p05_digit 16 j<2 := by decide +kernel

private theorem R10p05_bound_17 : ∀ j : Fin 22,R10p05_digit 17 j<2 := by decide +kernel

private theorem R10p05_bound_18 : ∀ j : Fin 22,R10p05_digit 18 j<2 := by decide +kernel

private theorem R10p05_bound_19 : ∀ j : Fin 22,R10p05_digit 19 j<2 := by decide +kernel

private theorem R10p05_bound_20 : ∀ j : Fin 22,R10p05_digit 20 j<2 := by decide +kernel

private theorem R10p05_bound_21 : ∀ j : Fin 22,R10p05_digit 21 j<2 := by decide +kernel

theorem R10p05_bound : ∀ i j : Fin 22,R10p05_digit i j<2 := by
  intro i j
  fin_cases i
  · exact R10p05_bound_00 j
  · exact R10p05_bound_01 j
  · exact R10p05_bound_02 j
  · exact R10p05_bound_03 j
  · exact R10p05_bound_04 j
  · exact R10p05_bound_05 j
  · exact R10p05_bound_06 j
  · exact R10p05_bound_07 j
  · exact R10p05_bound_08 j
  · exact R10p05_bound_09 j
  · exact R10p05_bound_10 j
  · exact R10p05_bound_11 j
  · exact R10p05_bound_12 j
  · exact R10p05_bound_13 j
  · exact R10p05_bound_14 j
  · exact R10p05_bound_15 j
  · exact R10p05_bound_16 j
  · exact R10p05_bound_17 j
  · exact R10p05_bound_18 j
  · exact R10p05_bound_19 j
  · exact R10p05_bound_20 j
  · exact R10p05_bound_21 j

private theorem R10p05_row_00 : pack 32 (R10p05_digit 0)=R10p05_rowCode 0 := by decide +kernel

private theorem R10p05_row_01 : pack 32 (R10p05_digit 1)=R10p05_rowCode 1 := by decide +kernel

private theorem R10p05_row_02 : pack 32 (R10p05_digit 2)=R10p05_rowCode 2 := by decide +kernel

private theorem R10p05_row_03 : pack 32 (R10p05_digit 3)=R10p05_rowCode 3 := by decide +kernel

private theorem R10p05_row_04 : pack 32 (R10p05_digit 4)=R10p05_rowCode 4 := by decide +kernel

private theorem R10p05_row_05 : pack 32 (R10p05_digit 5)=R10p05_rowCode 5 := by decide +kernel

private theorem R10p05_row_06 : pack 32 (R10p05_digit 6)=R10p05_rowCode 6 := by decide +kernel

private theorem R10p05_row_07 : pack 32 (R10p05_digit 7)=R10p05_rowCode 7 := by decide +kernel

private theorem R10p05_row_08 : pack 32 (R10p05_digit 8)=R10p05_rowCode 8 := by decide +kernel

private theorem R10p05_row_09 : pack 32 (R10p05_digit 9)=R10p05_rowCode 9 := by decide +kernel

private theorem R10p05_row_10 : pack 32 (R10p05_digit 10)=R10p05_rowCode 10 := by decide +kernel

private theorem R10p05_row_11 : pack 32 (R10p05_digit 11)=R10p05_rowCode 11 := by decide +kernel

private theorem R10p05_row_12 : pack 32 (R10p05_digit 12)=R10p05_rowCode 12 := by decide +kernel

private theorem R10p05_row_13 : pack 32 (R10p05_digit 13)=R10p05_rowCode 13 := by decide +kernel

private theorem R10p05_row_14 : pack 32 (R10p05_digit 14)=R10p05_rowCode 14 := by decide +kernel

private theorem R10p05_row_15 : pack 32 (R10p05_digit 15)=R10p05_rowCode 15 := by decide +kernel

private theorem R10p05_row_16 : pack 32 (R10p05_digit 16)=R10p05_rowCode 16 := by decide +kernel

private theorem R10p05_row_17 : pack 32 (R10p05_digit 17)=R10p05_rowCode 17 := by decide +kernel

private theorem R10p05_row_18 : pack 32 (R10p05_digit 18)=R10p05_rowCode 18 := by decide +kernel

private theorem R10p05_row_19 : pack 32 (R10p05_digit 19)=R10p05_rowCode 19 := by decide +kernel

private theorem R10p05_row_20 : pack 32 (R10p05_digit 20)=R10p05_rowCode 20 := by decide +kernel

private theorem R10p05_row_21 : pack 32 (R10p05_digit 21)=R10p05_rowCode 21 := by decide +kernel

theorem R10p05_row_binding : ∀ i : Fin 22,pack 32 (R10p05_digit i)=R10p05_rowCode i := by
  intro i
  fin_cases i
  · exact R10p05_row_00
  · exact R10p05_row_01
  · exact R10p05_row_02
  · exact R10p05_row_03
  · exact R10p05_row_04
  · exact R10p05_row_05
  · exact R10p05_row_06
  · exact R10p05_row_07
  · exact R10p05_row_08
  · exact R10p05_row_09
  · exact R10p05_row_10
  · exact R10p05_row_11
  · exact R10p05_row_12
  · exact R10p05_row_13
  · exact R10p05_row_14
  · exact R10p05_row_15
  · exact R10p05_row_16
  · exact R10p05_row_17
  · exact R10p05_row_18
  · exact R10p05_row_19
  · exact R10p05_row_20
  · exact R10p05_row_21

private theorem R10p05_column_00 : reversePack 32 (fun j : Fin 22 => R10p05_digit j 0)=R10p05_columnCode 0 := by decide +kernel

private theorem R10p05_column_01 : reversePack 32 (fun j : Fin 22 => R10p05_digit j 1)=R10p05_columnCode 1 := by decide +kernel

private theorem R10p05_column_02 : reversePack 32 (fun j : Fin 22 => R10p05_digit j 2)=R10p05_columnCode 2 := by decide +kernel

private theorem R10p05_column_03 : reversePack 32 (fun j : Fin 22 => R10p05_digit j 3)=R10p05_columnCode 3 := by decide +kernel

private theorem R10p05_column_04 : reversePack 32 (fun j : Fin 22 => R10p05_digit j 4)=R10p05_columnCode 4 := by decide +kernel

private theorem R10p05_column_05 : reversePack 32 (fun j : Fin 22 => R10p05_digit j 5)=R10p05_columnCode 5 := by decide +kernel

private theorem R10p05_column_06 : reversePack 32 (fun j : Fin 22 => R10p05_digit j 6)=R10p05_columnCode 6 := by decide +kernel

private theorem R10p05_column_07 : reversePack 32 (fun j : Fin 22 => R10p05_digit j 7)=R10p05_columnCode 7 := by decide +kernel

private theorem R10p05_column_08 : reversePack 32 (fun j : Fin 22 => R10p05_digit j 8)=R10p05_columnCode 8 := by decide +kernel

private theorem R10p05_column_09 : reversePack 32 (fun j : Fin 22 => R10p05_digit j 9)=R10p05_columnCode 9 := by decide +kernel

private theorem R10p05_column_10 : reversePack 32 (fun j : Fin 22 => R10p05_digit j 10)=R10p05_columnCode 10 := by decide +kernel

private theorem R10p05_column_11 : reversePack 32 (fun j : Fin 22 => R10p05_digit j 11)=R10p05_columnCode 11 := by decide +kernel

private theorem R10p05_column_12 : reversePack 32 (fun j : Fin 22 => R10p05_digit j 12)=R10p05_columnCode 12 := by decide +kernel

private theorem R10p05_column_13 : reversePack 32 (fun j : Fin 22 => R10p05_digit j 13)=R10p05_columnCode 13 := by decide +kernel

private theorem R10p05_column_14 : reversePack 32 (fun j : Fin 22 => R10p05_digit j 14)=R10p05_columnCode 14 := by decide +kernel

private theorem R10p05_column_15 : reversePack 32 (fun j : Fin 22 => R10p05_digit j 15)=R10p05_columnCode 15 := by decide +kernel

private theorem R10p05_column_16 : reversePack 32 (fun j : Fin 22 => R10p05_digit j 16)=R10p05_columnCode 16 := by decide +kernel

private theorem R10p05_column_17 : reversePack 32 (fun j : Fin 22 => R10p05_digit j 17)=R10p05_columnCode 17 := by decide +kernel

private theorem R10p05_column_18 : reversePack 32 (fun j : Fin 22 => R10p05_digit j 18)=R10p05_columnCode 18 := by decide +kernel

private theorem R10p05_column_19 : reversePack 32 (fun j : Fin 22 => R10p05_digit j 19)=R10p05_columnCode 19 := by decide +kernel

private theorem R10p05_column_20 : reversePack 32 (fun j : Fin 22 => R10p05_digit j 20)=R10p05_columnCode 20 := by decide +kernel

private theorem R10p05_column_21 : reversePack 32 (fun j : Fin 22 => R10p05_digit j 21)=R10p05_columnCode 21 := by decide +kernel

theorem R10p05_column_binding : ∀ i : Fin 22,reversePack 32 (fun j : Fin 22 => R10p05_digit j i)=R10p05_columnCode i := by
  intro i
  fin_cases i
  · exact R10p05_column_00
  · exact R10p05_column_01
  · exact R10p05_column_02
  · exact R10p05_column_03
  · exact R10p05_column_04
  · exact R10p05_column_05
  · exact R10p05_column_06
  · exact R10p05_column_07
  · exact R10p05_column_08
  · exact R10p05_column_09
  · exact R10p05_column_10
  · exact R10p05_column_11
  · exact R10p05_column_12
  · exact R10p05_column_13
  · exact R10p05_column_14
  · exact R10p05_column_15
  · exact R10p05_column_16
  · exact R10p05_column_17
  · exact R10p05_column_18
  · exact R10p05_column_19
  · exact R10p05_column_20
  · exact R10p05_column_21

def R10p05_data : PackedData 22 2 32 where
  raw := R10p05_digit
  digit_lt := R10p05_bound
  rowCode := R10p05_rowCode
  columnCode := R10p05_columnCode
  row_binding := R10p05_row_binding
  column_binding := R10p05_column_binding

def R10p06_lowColumnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 2764674
  | 1 => 3138501
  | 2 => 3128269
  | 3 => 962539
  | 4 => 2912478
  | 5 => 3058540
  | 6 => 684036
  | 7 => 2353295
  | 8 => 3248986
  | 9 => 3414958
  | 10 => 2627805
  | 11 => 3691295
  | 12 => 3545182
  | 13 => 3837803
  | 14 => 2937291
  | 15 => 2303142
  | 16 => 1136694
  | 17 => 4190157
  | 18 => 3070995
  | 19 => 2101840
  | 20 => 472064
  | 21 => 2170568
  | _ => 0

def R10p06_rowCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 1276626883035312004605707296
  | 1 => 1239187962710953345936293889
  | 2 => 39932332169257141299840032
  | 3 => 40564857894148243737412734321664
  | 4 => 40853230223427241001891135488
  | 5 => 1246741645000918161195008
  | 6 => 40604471975405339842193755505696
  | 7 => 40564857931889093160821305934881
  | 8 => 38686843748842079357273121
  | 9 => 40604471974223630238053220516897
  | 10 => 41833746471012908648904276344833
  | 11 => 40566097041932721081702865208321
  | 12 => 41873323038935589146295954048000
  | 13 => 1267689323633388932622923629601
  | 14 => 1277835771960312587529224224
  | 15 => 1276626882998158407225082912
  | 16 => 41832509739862549396245004157984
  | 17 => 1268927263710720722549847655457
  | 18 => 1268927227075487027311617803296
  | 19 => 1276626883035311971354313761
  | 20 => 39894590129757495693934592
  | 21 => 40605709953223593149441567097889
  | _ => 0

def R10p06_columnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 1267650601446904587662578942977
  | 1 => 40604433327558042911152853255169
  | 2 => 40605671267597329452477671572481
  | 3 => 41833708995494282293419390829568
  | 4 => 1308541346110398138694781404161
  | 5 => 40853268039216563310526759937
  | 6 => 39614081257132205115016479744
  | 7 => 41873321830008580546215174733825
  | 8 => 1268927263710720757699859972129
  | 9 => 1308503831669105756651265228833
  | 10 => 40605709953185510709858616214529
  | 11 => 41873360514492261911467225252897
  | 12 => 1308541344929807642743406624801
  | 13 => 41833708994313690671602467865633
  | 14 => 41833707786567272636707902620673
  | 15 => 1307265891591808835536626384897
  | 16 => 1307304576037410014174912708640
  | 17 => 40605671267597365446124678186017
  | 18 => 41832508493157835107441528833025
  | 19 => 38723406312487779731243009
  | 20 => 36065080937316352
  | 21 => 1237978999998975335410434049
  | _ => 0

def R10p06_digit (i j : Fin 22) : ℕ := packedDigit 1 (R10p06_lowColumnCode j) i.val

private theorem R10p06_bound_00 : ∀ j : Fin 22,R10p06_digit 0 j<2 := by decide +kernel

private theorem R10p06_bound_01 : ∀ j : Fin 22,R10p06_digit 1 j<2 := by decide +kernel

private theorem R10p06_bound_02 : ∀ j : Fin 22,R10p06_digit 2 j<2 := by decide +kernel

private theorem R10p06_bound_03 : ∀ j : Fin 22,R10p06_digit 3 j<2 := by decide +kernel

private theorem R10p06_bound_04 : ∀ j : Fin 22,R10p06_digit 4 j<2 := by decide +kernel

private theorem R10p06_bound_05 : ∀ j : Fin 22,R10p06_digit 5 j<2 := by decide +kernel

private theorem R10p06_bound_06 : ∀ j : Fin 22,R10p06_digit 6 j<2 := by decide +kernel

private theorem R10p06_bound_07 : ∀ j : Fin 22,R10p06_digit 7 j<2 := by decide +kernel

private theorem R10p06_bound_08 : ∀ j : Fin 22,R10p06_digit 8 j<2 := by decide +kernel

private theorem R10p06_bound_09 : ∀ j : Fin 22,R10p06_digit 9 j<2 := by decide +kernel

private theorem R10p06_bound_10 : ∀ j : Fin 22,R10p06_digit 10 j<2 := by decide +kernel

private theorem R10p06_bound_11 : ∀ j : Fin 22,R10p06_digit 11 j<2 := by decide +kernel

private theorem R10p06_bound_12 : ∀ j : Fin 22,R10p06_digit 12 j<2 := by decide +kernel

private theorem R10p06_bound_13 : ∀ j : Fin 22,R10p06_digit 13 j<2 := by decide +kernel

private theorem R10p06_bound_14 : ∀ j : Fin 22,R10p06_digit 14 j<2 := by decide +kernel

private theorem R10p06_bound_15 : ∀ j : Fin 22,R10p06_digit 15 j<2 := by decide +kernel

private theorem R10p06_bound_16 : ∀ j : Fin 22,R10p06_digit 16 j<2 := by decide +kernel

private theorem R10p06_bound_17 : ∀ j : Fin 22,R10p06_digit 17 j<2 := by decide +kernel

private theorem R10p06_bound_18 : ∀ j : Fin 22,R10p06_digit 18 j<2 := by decide +kernel

private theorem R10p06_bound_19 : ∀ j : Fin 22,R10p06_digit 19 j<2 := by decide +kernel

private theorem R10p06_bound_20 : ∀ j : Fin 22,R10p06_digit 20 j<2 := by decide +kernel

private theorem R10p06_bound_21 : ∀ j : Fin 22,R10p06_digit 21 j<2 := by decide +kernel

theorem R10p06_bound : ∀ i j : Fin 22,R10p06_digit i j<2 := by
  intro i j
  fin_cases i
  · exact R10p06_bound_00 j
  · exact R10p06_bound_01 j
  · exact R10p06_bound_02 j
  · exact R10p06_bound_03 j
  · exact R10p06_bound_04 j
  · exact R10p06_bound_05 j
  · exact R10p06_bound_06 j
  · exact R10p06_bound_07 j
  · exact R10p06_bound_08 j
  · exact R10p06_bound_09 j
  · exact R10p06_bound_10 j
  · exact R10p06_bound_11 j
  · exact R10p06_bound_12 j
  · exact R10p06_bound_13 j
  · exact R10p06_bound_14 j
  · exact R10p06_bound_15 j
  · exact R10p06_bound_16 j
  · exact R10p06_bound_17 j
  · exact R10p06_bound_18 j
  · exact R10p06_bound_19 j
  · exact R10p06_bound_20 j
  · exact R10p06_bound_21 j

private theorem R10p06_row_00 : pack 32 (R10p06_digit 0)=R10p06_rowCode 0 := by decide +kernel

private theorem R10p06_row_01 : pack 32 (R10p06_digit 1)=R10p06_rowCode 1 := by decide +kernel

private theorem R10p06_row_02 : pack 32 (R10p06_digit 2)=R10p06_rowCode 2 := by decide +kernel

private theorem R10p06_row_03 : pack 32 (R10p06_digit 3)=R10p06_rowCode 3 := by decide +kernel

private theorem R10p06_row_04 : pack 32 (R10p06_digit 4)=R10p06_rowCode 4 := by decide +kernel

private theorem R10p06_row_05 : pack 32 (R10p06_digit 5)=R10p06_rowCode 5 := by decide +kernel

private theorem R10p06_row_06 : pack 32 (R10p06_digit 6)=R10p06_rowCode 6 := by decide +kernel

private theorem R10p06_row_07 : pack 32 (R10p06_digit 7)=R10p06_rowCode 7 := by decide +kernel

private theorem R10p06_row_08 : pack 32 (R10p06_digit 8)=R10p06_rowCode 8 := by decide +kernel

private theorem R10p06_row_09 : pack 32 (R10p06_digit 9)=R10p06_rowCode 9 := by decide +kernel

private theorem R10p06_row_10 : pack 32 (R10p06_digit 10)=R10p06_rowCode 10 := by decide +kernel

private theorem R10p06_row_11 : pack 32 (R10p06_digit 11)=R10p06_rowCode 11 := by decide +kernel

private theorem R10p06_row_12 : pack 32 (R10p06_digit 12)=R10p06_rowCode 12 := by decide +kernel

private theorem R10p06_row_13 : pack 32 (R10p06_digit 13)=R10p06_rowCode 13 := by decide +kernel

private theorem R10p06_row_14 : pack 32 (R10p06_digit 14)=R10p06_rowCode 14 := by decide +kernel

private theorem R10p06_row_15 : pack 32 (R10p06_digit 15)=R10p06_rowCode 15 := by decide +kernel

private theorem R10p06_row_16 : pack 32 (R10p06_digit 16)=R10p06_rowCode 16 := by decide +kernel

private theorem R10p06_row_17 : pack 32 (R10p06_digit 17)=R10p06_rowCode 17 := by decide +kernel

private theorem R10p06_row_18 : pack 32 (R10p06_digit 18)=R10p06_rowCode 18 := by decide +kernel

private theorem R10p06_row_19 : pack 32 (R10p06_digit 19)=R10p06_rowCode 19 := by decide +kernel

private theorem R10p06_row_20 : pack 32 (R10p06_digit 20)=R10p06_rowCode 20 := by decide +kernel

private theorem R10p06_row_21 : pack 32 (R10p06_digit 21)=R10p06_rowCode 21 := by decide +kernel

theorem R10p06_row_binding : ∀ i : Fin 22,pack 32 (R10p06_digit i)=R10p06_rowCode i := by
  intro i
  fin_cases i
  · exact R10p06_row_00
  · exact R10p06_row_01
  · exact R10p06_row_02
  · exact R10p06_row_03
  · exact R10p06_row_04
  · exact R10p06_row_05
  · exact R10p06_row_06
  · exact R10p06_row_07
  · exact R10p06_row_08
  · exact R10p06_row_09
  · exact R10p06_row_10
  · exact R10p06_row_11
  · exact R10p06_row_12
  · exact R10p06_row_13
  · exact R10p06_row_14
  · exact R10p06_row_15
  · exact R10p06_row_16
  · exact R10p06_row_17
  · exact R10p06_row_18
  · exact R10p06_row_19
  · exact R10p06_row_20
  · exact R10p06_row_21

private theorem R10p06_column_00 : reversePack 32 (fun j : Fin 22 => R10p06_digit j 0)=R10p06_columnCode 0 := by decide +kernel

private theorem R10p06_column_01 : reversePack 32 (fun j : Fin 22 => R10p06_digit j 1)=R10p06_columnCode 1 := by decide +kernel

private theorem R10p06_column_02 : reversePack 32 (fun j : Fin 22 => R10p06_digit j 2)=R10p06_columnCode 2 := by decide +kernel

private theorem R10p06_column_03 : reversePack 32 (fun j : Fin 22 => R10p06_digit j 3)=R10p06_columnCode 3 := by decide +kernel

private theorem R10p06_column_04 : reversePack 32 (fun j : Fin 22 => R10p06_digit j 4)=R10p06_columnCode 4 := by decide +kernel

private theorem R10p06_column_05 : reversePack 32 (fun j : Fin 22 => R10p06_digit j 5)=R10p06_columnCode 5 := by decide +kernel

private theorem R10p06_column_06 : reversePack 32 (fun j : Fin 22 => R10p06_digit j 6)=R10p06_columnCode 6 := by decide +kernel

private theorem R10p06_column_07 : reversePack 32 (fun j : Fin 22 => R10p06_digit j 7)=R10p06_columnCode 7 := by decide +kernel

private theorem R10p06_column_08 : reversePack 32 (fun j : Fin 22 => R10p06_digit j 8)=R10p06_columnCode 8 := by decide +kernel

private theorem R10p06_column_09 : reversePack 32 (fun j : Fin 22 => R10p06_digit j 9)=R10p06_columnCode 9 := by decide +kernel

private theorem R10p06_column_10 : reversePack 32 (fun j : Fin 22 => R10p06_digit j 10)=R10p06_columnCode 10 := by decide +kernel

private theorem R10p06_column_11 : reversePack 32 (fun j : Fin 22 => R10p06_digit j 11)=R10p06_columnCode 11 := by decide +kernel

private theorem R10p06_column_12 : reversePack 32 (fun j : Fin 22 => R10p06_digit j 12)=R10p06_columnCode 12 := by decide +kernel

private theorem R10p06_column_13 : reversePack 32 (fun j : Fin 22 => R10p06_digit j 13)=R10p06_columnCode 13 := by decide +kernel

private theorem R10p06_column_14 : reversePack 32 (fun j : Fin 22 => R10p06_digit j 14)=R10p06_columnCode 14 := by decide +kernel

private theorem R10p06_column_15 : reversePack 32 (fun j : Fin 22 => R10p06_digit j 15)=R10p06_columnCode 15 := by decide +kernel

private theorem R10p06_column_16 : reversePack 32 (fun j : Fin 22 => R10p06_digit j 16)=R10p06_columnCode 16 := by decide +kernel

private theorem R10p06_column_17 : reversePack 32 (fun j : Fin 22 => R10p06_digit j 17)=R10p06_columnCode 17 := by decide +kernel

private theorem R10p06_column_18 : reversePack 32 (fun j : Fin 22 => R10p06_digit j 18)=R10p06_columnCode 18 := by decide +kernel

private theorem R10p06_column_19 : reversePack 32 (fun j : Fin 22 => R10p06_digit j 19)=R10p06_columnCode 19 := by decide +kernel

private theorem R10p06_column_20 : reversePack 32 (fun j : Fin 22 => R10p06_digit j 20)=R10p06_columnCode 20 := by decide +kernel

private theorem R10p06_column_21 : reversePack 32 (fun j : Fin 22 => R10p06_digit j 21)=R10p06_columnCode 21 := by decide +kernel

theorem R10p06_column_binding : ∀ i : Fin 22,reversePack 32 (fun j : Fin 22 => R10p06_digit j i)=R10p06_columnCode i := by
  intro i
  fin_cases i
  · exact R10p06_column_00
  · exact R10p06_column_01
  · exact R10p06_column_02
  · exact R10p06_column_03
  · exact R10p06_column_04
  · exact R10p06_column_05
  · exact R10p06_column_06
  · exact R10p06_column_07
  · exact R10p06_column_08
  · exact R10p06_column_09
  · exact R10p06_column_10
  · exact R10p06_column_11
  · exact R10p06_column_12
  · exact R10p06_column_13
  · exact R10p06_column_14
  · exact R10p06_column_15
  · exact R10p06_column_16
  · exact R10p06_column_17
  · exact R10p06_column_18
  · exact R10p06_column_19
  · exact R10p06_column_20
  · exact R10p06_column_21

def R10p06_data : PackedData 22 2 32 where
  raw := R10p06_digit
  digit_lt := R10p06_bound
  rowCode := R10p06_rowCode
  columnCode := R10p06_columnCode
  row_binding := R10p06_row_binding
  column_binding := R10p06_column_binding

end SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoCaches11
