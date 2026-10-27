import SymmetricSubgroupAsymptotics.MatrixKroneckerProductReflection
import Mathlib.Tactic.FinCases

/-! Fixed Co2 binary22 shared caches. Every digit and pack binding is kernel checked. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoCaches04
open MatrixKroneckerProductReflection MatrixKroneckerDotReflection
open MatrixNaturalRowDotReflection SmallNaturalMatrixProductReflection

def R06p06_lowColumnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 2528125
  | 1 => 1200242
  | 2 => 1337362
  | 3 => 3418976
  | 4 => 2867953
  | 5 => 4048963
  | 6 => 4012784
  | 7 => 2859730
  | 8 => 4152512
  | 9 => 182339
  | 10 => 2017458
  | 11 => 2273313
  | 12 => 2923202
  | 13 => 1497778
  | 14 => 12960
  | 15 => 1325284
  | 16 => 1462992
  | 17 => 3418688
  | 18 => 1106514
  | 19 => 3306192
  | 20 => 2151120
  | 21 => 3416064
  | _ => 0

def R06p06_rowCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 36063981425655809
  | 1 => 1237940077332951045597299744
  | 2 => 37778931862957161709569
  | 3 => 1
  | 4 => 1308503830487361179280309486625
  | 5 => 38996454126519992746017
  | 6 => 1308542553856779054112259997729
  | 7 => 1307265929408752205284101849088
  | 8 => 32769
  | 9 => 1308542517295332263736011423745
  | 10 => 1099511627776
  | 11 => 38723443207102927676146688
  | 12 => 1307265929408787108146853183521
  | 13 => 40605709953185545577606789760000
  | 14 => 1308503830487361215528793277472
  | 15 => 1268888540305598381339320516609
  | 16 => 1134979710976
  | 17 => 39615290219882462588536094753
  | 18 => 40564859139672367530266981336065
  | 19 => 1154048539493400576
  | 20 => 40605711160967632157834045588512
  | 21 => 41872122574416119037758173904897
  | _ => 0

def R06p06_columnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 40605711160968783987523573547009
  | 1 => 1267690532559208582435363094560
  | 2 => 1267689285854458196664072044576
  | 3 => 1246742799014237780869153
  | 4 => 40564859140816064535871915820033
  | 5 => 41832469845310503238283741398049
  | 6 => 39933512724850125769311265
  | 7 => 1267689324815133475910093636609
  | 8 => 38959560673590265283617
  | 9 => 41832469845310503238283708858368
  | 10 => 1267690495960869430912221217824
  | 11 => 40564820416229160498808635785217
  | 12 => 1267650639188906967761235772417
  | 13 => 1267690495962022387601200152608
  | 14 => 1210107564193135076573184
  | 15 => 39615329142476429284310286368
  | 16 => 38724586904108531503366176
  | 17 => 37780085911461187059745
  | 18 => 1267689323634541855227007467552
  | 19 => 38724586904109631014961185
  | 20 => 38724586904108532576026625
  | 21 => 1099511660577
  | _ => 0

def R06p06_digit (i j : Fin 22) : ℕ := packedDigit 1 (R06p06_lowColumnCode j) i.val

private theorem R06p06_bound_00 : ∀ j : Fin 22,R06p06_digit 0 j<2 := by decide +kernel

private theorem R06p06_bound_01 : ∀ j : Fin 22,R06p06_digit 1 j<2 := by decide +kernel

private theorem R06p06_bound_02 : ∀ j : Fin 22,R06p06_digit 2 j<2 := by decide +kernel

private theorem R06p06_bound_03 : ∀ j : Fin 22,R06p06_digit 3 j<2 := by decide +kernel

private theorem R06p06_bound_04 : ∀ j : Fin 22,R06p06_digit 4 j<2 := by decide +kernel

private theorem R06p06_bound_05 : ∀ j : Fin 22,R06p06_digit 5 j<2 := by decide +kernel

private theorem R06p06_bound_06 : ∀ j : Fin 22,R06p06_digit 6 j<2 := by decide +kernel

private theorem R06p06_bound_07 : ∀ j : Fin 22,R06p06_digit 7 j<2 := by decide +kernel

private theorem R06p06_bound_08 : ∀ j : Fin 22,R06p06_digit 8 j<2 := by decide +kernel

private theorem R06p06_bound_09 : ∀ j : Fin 22,R06p06_digit 9 j<2 := by decide +kernel

private theorem R06p06_bound_10 : ∀ j : Fin 22,R06p06_digit 10 j<2 := by decide +kernel

private theorem R06p06_bound_11 : ∀ j : Fin 22,R06p06_digit 11 j<2 := by decide +kernel

private theorem R06p06_bound_12 : ∀ j : Fin 22,R06p06_digit 12 j<2 := by decide +kernel

private theorem R06p06_bound_13 : ∀ j : Fin 22,R06p06_digit 13 j<2 := by decide +kernel

private theorem R06p06_bound_14 : ∀ j : Fin 22,R06p06_digit 14 j<2 := by decide +kernel

private theorem R06p06_bound_15 : ∀ j : Fin 22,R06p06_digit 15 j<2 := by decide +kernel

private theorem R06p06_bound_16 : ∀ j : Fin 22,R06p06_digit 16 j<2 := by decide +kernel

private theorem R06p06_bound_17 : ∀ j : Fin 22,R06p06_digit 17 j<2 := by decide +kernel

private theorem R06p06_bound_18 : ∀ j : Fin 22,R06p06_digit 18 j<2 := by decide +kernel

private theorem R06p06_bound_19 : ∀ j : Fin 22,R06p06_digit 19 j<2 := by decide +kernel

private theorem R06p06_bound_20 : ∀ j : Fin 22,R06p06_digit 20 j<2 := by decide +kernel

private theorem R06p06_bound_21 : ∀ j : Fin 22,R06p06_digit 21 j<2 := by decide +kernel

theorem R06p06_bound : ∀ i j : Fin 22,R06p06_digit i j<2 := by
  intro i j
  fin_cases i
  · exact R06p06_bound_00 j
  · exact R06p06_bound_01 j
  · exact R06p06_bound_02 j
  · exact R06p06_bound_03 j
  · exact R06p06_bound_04 j
  · exact R06p06_bound_05 j
  · exact R06p06_bound_06 j
  · exact R06p06_bound_07 j
  · exact R06p06_bound_08 j
  · exact R06p06_bound_09 j
  · exact R06p06_bound_10 j
  · exact R06p06_bound_11 j
  · exact R06p06_bound_12 j
  · exact R06p06_bound_13 j
  · exact R06p06_bound_14 j
  · exact R06p06_bound_15 j
  · exact R06p06_bound_16 j
  · exact R06p06_bound_17 j
  · exact R06p06_bound_18 j
  · exact R06p06_bound_19 j
  · exact R06p06_bound_20 j
  · exact R06p06_bound_21 j

private theorem R06p06_row_00 : pack 32 (R06p06_digit 0)=R06p06_rowCode 0 := by decide +kernel

private theorem R06p06_row_01 : pack 32 (R06p06_digit 1)=R06p06_rowCode 1 := by decide +kernel

private theorem R06p06_row_02 : pack 32 (R06p06_digit 2)=R06p06_rowCode 2 := by decide +kernel

private theorem R06p06_row_03 : pack 32 (R06p06_digit 3)=R06p06_rowCode 3 := by decide +kernel

private theorem R06p06_row_04 : pack 32 (R06p06_digit 4)=R06p06_rowCode 4 := by decide +kernel

private theorem R06p06_row_05 : pack 32 (R06p06_digit 5)=R06p06_rowCode 5 := by decide +kernel

private theorem R06p06_row_06 : pack 32 (R06p06_digit 6)=R06p06_rowCode 6 := by decide +kernel

private theorem R06p06_row_07 : pack 32 (R06p06_digit 7)=R06p06_rowCode 7 := by decide +kernel

private theorem R06p06_row_08 : pack 32 (R06p06_digit 8)=R06p06_rowCode 8 := by decide +kernel

private theorem R06p06_row_09 : pack 32 (R06p06_digit 9)=R06p06_rowCode 9 := by decide +kernel

private theorem R06p06_row_10 : pack 32 (R06p06_digit 10)=R06p06_rowCode 10 := by decide +kernel

private theorem R06p06_row_11 : pack 32 (R06p06_digit 11)=R06p06_rowCode 11 := by decide +kernel

private theorem R06p06_row_12 : pack 32 (R06p06_digit 12)=R06p06_rowCode 12 := by decide +kernel

private theorem R06p06_row_13 : pack 32 (R06p06_digit 13)=R06p06_rowCode 13 := by decide +kernel

private theorem R06p06_row_14 : pack 32 (R06p06_digit 14)=R06p06_rowCode 14 := by decide +kernel

private theorem R06p06_row_15 : pack 32 (R06p06_digit 15)=R06p06_rowCode 15 := by decide +kernel

private theorem R06p06_row_16 : pack 32 (R06p06_digit 16)=R06p06_rowCode 16 := by decide +kernel

private theorem R06p06_row_17 : pack 32 (R06p06_digit 17)=R06p06_rowCode 17 := by decide +kernel

private theorem R06p06_row_18 : pack 32 (R06p06_digit 18)=R06p06_rowCode 18 := by decide +kernel

private theorem R06p06_row_19 : pack 32 (R06p06_digit 19)=R06p06_rowCode 19 := by decide +kernel

private theorem R06p06_row_20 : pack 32 (R06p06_digit 20)=R06p06_rowCode 20 := by decide +kernel

private theorem R06p06_row_21 : pack 32 (R06p06_digit 21)=R06p06_rowCode 21 := by decide +kernel

theorem R06p06_row_binding : ∀ i : Fin 22,pack 32 (R06p06_digit i)=R06p06_rowCode i := by
  intro i
  fin_cases i
  · exact R06p06_row_00
  · exact R06p06_row_01
  · exact R06p06_row_02
  · exact R06p06_row_03
  · exact R06p06_row_04
  · exact R06p06_row_05
  · exact R06p06_row_06
  · exact R06p06_row_07
  · exact R06p06_row_08
  · exact R06p06_row_09
  · exact R06p06_row_10
  · exact R06p06_row_11
  · exact R06p06_row_12
  · exact R06p06_row_13
  · exact R06p06_row_14
  · exact R06p06_row_15
  · exact R06p06_row_16
  · exact R06p06_row_17
  · exact R06p06_row_18
  · exact R06p06_row_19
  · exact R06p06_row_20
  · exact R06p06_row_21

private theorem R06p06_column_00 : reversePack 32 (fun j : Fin 22 => R06p06_digit j 0)=R06p06_columnCode 0 := by decide +kernel

private theorem R06p06_column_01 : reversePack 32 (fun j : Fin 22 => R06p06_digit j 1)=R06p06_columnCode 1 := by decide +kernel

private theorem R06p06_column_02 : reversePack 32 (fun j : Fin 22 => R06p06_digit j 2)=R06p06_columnCode 2 := by decide +kernel

private theorem R06p06_column_03 : reversePack 32 (fun j : Fin 22 => R06p06_digit j 3)=R06p06_columnCode 3 := by decide +kernel

private theorem R06p06_column_04 : reversePack 32 (fun j : Fin 22 => R06p06_digit j 4)=R06p06_columnCode 4 := by decide +kernel

private theorem R06p06_column_05 : reversePack 32 (fun j : Fin 22 => R06p06_digit j 5)=R06p06_columnCode 5 := by decide +kernel

private theorem R06p06_column_06 : reversePack 32 (fun j : Fin 22 => R06p06_digit j 6)=R06p06_columnCode 6 := by decide +kernel

private theorem R06p06_column_07 : reversePack 32 (fun j : Fin 22 => R06p06_digit j 7)=R06p06_columnCode 7 := by decide +kernel

private theorem R06p06_column_08 : reversePack 32 (fun j : Fin 22 => R06p06_digit j 8)=R06p06_columnCode 8 := by decide +kernel

private theorem R06p06_column_09 : reversePack 32 (fun j : Fin 22 => R06p06_digit j 9)=R06p06_columnCode 9 := by decide +kernel

private theorem R06p06_column_10 : reversePack 32 (fun j : Fin 22 => R06p06_digit j 10)=R06p06_columnCode 10 := by decide +kernel

private theorem R06p06_column_11 : reversePack 32 (fun j : Fin 22 => R06p06_digit j 11)=R06p06_columnCode 11 := by decide +kernel

private theorem R06p06_column_12 : reversePack 32 (fun j : Fin 22 => R06p06_digit j 12)=R06p06_columnCode 12 := by decide +kernel

private theorem R06p06_column_13 : reversePack 32 (fun j : Fin 22 => R06p06_digit j 13)=R06p06_columnCode 13 := by decide +kernel

private theorem R06p06_column_14 : reversePack 32 (fun j : Fin 22 => R06p06_digit j 14)=R06p06_columnCode 14 := by decide +kernel

private theorem R06p06_column_15 : reversePack 32 (fun j : Fin 22 => R06p06_digit j 15)=R06p06_columnCode 15 := by decide +kernel

private theorem R06p06_column_16 : reversePack 32 (fun j : Fin 22 => R06p06_digit j 16)=R06p06_columnCode 16 := by decide +kernel

private theorem R06p06_column_17 : reversePack 32 (fun j : Fin 22 => R06p06_digit j 17)=R06p06_columnCode 17 := by decide +kernel

private theorem R06p06_column_18 : reversePack 32 (fun j : Fin 22 => R06p06_digit j 18)=R06p06_columnCode 18 := by decide +kernel

private theorem R06p06_column_19 : reversePack 32 (fun j : Fin 22 => R06p06_digit j 19)=R06p06_columnCode 19 := by decide +kernel

private theorem R06p06_column_20 : reversePack 32 (fun j : Fin 22 => R06p06_digit j 20)=R06p06_columnCode 20 := by decide +kernel

private theorem R06p06_column_21 : reversePack 32 (fun j : Fin 22 => R06p06_digit j 21)=R06p06_columnCode 21 := by decide +kernel

theorem R06p06_column_binding : ∀ i : Fin 22,reversePack 32 (fun j : Fin 22 => R06p06_digit j i)=R06p06_columnCode i := by
  intro i
  fin_cases i
  · exact R06p06_column_00
  · exact R06p06_column_01
  · exact R06p06_column_02
  · exact R06p06_column_03
  · exact R06p06_column_04
  · exact R06p06_column_05
  · exact R06p06_column_06
  · exact R06p06_column_07
  · exact R06p06_column_08
  · exact R06p06_column_09
  · exact R06p06_column_10
  · exact R06p06_column_11
  · exact R06p06_column_12
  · exact R06p06_column_13
  · exact R06p06_column_14
  · exact R06p06_column_15
  · exact R06p06_column_16
  · exact R06p06_column_17
  · exact R06p06_column_18
  · exact R06p06_column_19
  · exact R06p06_column_20
  · exact R06p06_column_21

def R06p06_data : PackedData 22 2 32 where
  raw := R06p06_digit
  digit_lt := R06p06_bound
  rowCode := R06p06_rowCode
  columnCode := R06p06_columnCode
  row_binding := R06p06_row_binding
  column_binding := R06p06_column_binding

def R06p07_lowColumnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 2065106
  | 1 => 2519154
  | 2 => 2834909
  | 3 => 3580454
  | 4 => 3774480
  | 5 => 1487266
  | 6 => 415888
  | 7 => 406259
  | 8 => 1486978
  | 9 => 2052737
  | 10 => 4010160
  | 11 => 1810066
  | 12 => 2118273
  | 13 => 2928674
  | 14 => 422515
  | 15 => 917504
  | 16 => 3416064
  | 17 => 2400802
  | 18 => 2269730
  | 19 => 414416
  | 20 => 1048576
  | 21 => 2151120
  | _ => 0

def R06p07_rowCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 1181744577440749978624
  | 1 => 1276626883034187204244045857
  | 2 => 33792
  | 3 => 1024
  | 4 => 40604433289741101792141046187041
  | 5 => 1276626882999283207620296736
  | 6 => 40604433289741064637443045590049
  | 7 => 40604433288561663129212157953025
  | 8 => 33555456
  | 9 => 40605709915407766671337533243393
  | 10 => 36028797018963968
  | 11 => 36028798093754368
  | 12 => 40604433289779148238076989407264
  | 13 => 1277835808818898936306630688
  | 14 => 40604433289742217594098738529312
  | 15 => 40566095833005783414346976624641
  | 16 => 37189881298945025
  | 17 => 40852060255977097862613861409
  | 18 => 39654014805597585600787021857
  | 19 => 37815862540985879757825
  | 20 => 1267651809154086207106722070529
  | 21 => 40566097041932721046484100875296
  | _ => 0

def R06p07_columnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 1267689324815133474810582041632
  | 1 => 1267690532559208583534874755073
  | 2 => 40605709953222403036956150727681
  | 3 => 1307265890412334107527843184673
  | 4 => 38685626228829218976826401
  | 5 => 1267651810371534161275666858016
  | 6 => 38686806820449969641652224
  | 7 => 41832509741044293973617035739136
  | 8 => 1267650601408821058499073048608
  | 9 => 40564819208485085425335287186464
  | 10 => 39895732638939764093912097
  | 11 => 1267689287036238801734718194720
  | 12 => 40564819208485085425335252549633
  | 13 => 1267651809154049052410835403777
  | 14 => 41832509739863702352933984174080
  | 15 => 1082368
  | 16 => 1099511660577
  | 17 => 1267651809155201938731070160897
  | 18 => 1267651809155201938731071176705
  | 19 => 38724586904108531503366144
  | 20 => 32
  | 21 => 38724586904108532576026625
  | _ => 0

def R06p07_digit (i j : Fin 22) : ℕ := packedDigit 1 (R06p07_lowColumnCode j) i.val

private theorem R06p07_bound_00 : ∀ j : Fin 22,R06p07_digit 0 j<2 := by decide +kernel

private theorem R06p07_bound_01 : ∀ j : Fin 22,R06p07_digit 1 j<2 := by decide +kernel

private theorem R06p07_bound_02 : ∀ j : Fin 22,R06p07_digit 2 j<2 := by decide +kernel

private theorem R06p07_bound_03 : ∀ j : Fin 22,R06p07_digit 3 j<2 := by decide +kernel

private theorem R06p07_bound_04 : ∀ j : Fin 22,R06p07_digit 4 j<2 := by decide +kernel

private theorem R06p07_bound_05 : ∀ j : Fin 22,R06p07_digit 5 j<2 := by decide +kernel

private theorem R06p07_bound_06 : ∀ j : Fin 22,R06p07_digit 6 j<2 := by decide +kernel

private theorem R06p07_bound_07 : ∀ j : Fin 22,R06p07_digit 7 j<2 := by decide +kernel

private theorem R06p07_bound_08 : ∀ j : Fin 22,R06p07_digit 8 j<2 := by decide +kernel

private theorem R06p07_bound_09 : ∀ j : Fin 22,R06p07_digit 9 j<2 := by decide +kernel

private theorem R06p07_bound_10 : ∀ j : Fin 22,R06p07_digit 10 j<2 := by decide +kernel

private theorem R06p07_bound_11 : ∀ j : Fin 22,R06p07_digit 11 j<2 := by decide +kernel

private theorem R06p07_bound_12 : ∀ j : Fin 22,R06p07_digit 12 j<2 := by decide +kernel

private theorem R06p07_bound_13 : ∀ j : Fin 22,R06p07_digit 13 j<2 := by decide +kernel

private theorem R06p07_bound_14 : ∀ j : Fin 22,R06p07_digit 14 j<2 := by decide +kernel

private theorem R06p07_bound_15 : ∀ j : Fin 22,R06p07_digit 15 j<2 := by decide +kernel

private theorem R06p07_bound_16 : ∀ j : Fin 22,R06p07_digit 16 j<2 := by decide +kernel

private theorem R06p07_bound_17 : ∀ j : Fin 22,R06p07_digit 17 j<2 := by decide +kernel

private theorem R06p07_bound_18 : ∀ j : Fin 22,R06p07_digit 18 j<2 := by decide +kernel

private theorem R06p07_bound_19 : ∀ j : Fin 22,R06p07_digit 19 j<2 := by decide +kernel

private theorem R06p07_bound_20 : ∀ j : Fin 22,R06p07_digit 20 j<2 := by decide +kernel

private theorem R06p07_bound_21 : ∀ j : Fin 22,R06p07_digit 21 j<2 := by decide +kernel

theorem R06p07_bound : ∀ i j : Fin 22,R06p07_digit i j<2 := by
  intro i j
  fin_cases i
  · exact R06p07_bound_00 j
  · exact R06p07_bound_01 j
  · exact R06p07_bound_02 j
  · exact R06p07_bound_03 j
  · exact R06p07_bound_04 j
  · exact R06p07_bound_05 j
  · exact R06p07_bound_06 j
  · exact R06p07_bound_07 j
  · exact R06p07_bound_08 j
  · exact R06p07_bound_09 j
  · exact R06p07_bound_10 j
  · exact R06p07_bound_11 j
  · exact R06p07_bound_12 j
  · exact R06p07_bound_13 j
  · exact R06p07_bound_14 j
  · exact R06p07_bound_15 j
  · exact R06p07_bound_16 j
  · exact R06p07_bound_17 j
  · exact R06p07_bound_18 j
  · exact R06p07_bound_19 j
  · exact R06p07_bound_20 j
  · exact R06p07_bound_21 j

private theorem R06p07_row_00 : pack 32 (R06p07_digit 0)=R06p07_rowCode 0 := by decide +kernel

private theorem R06p07_row_01 : pack 32 (R06p07_digit 1)=R06p07_rowCode 1 := by decide +kernel

private theorem R06p07_row_02 : pack 32 (R06p07_digit 2)=R06p07_rowCode 2 := by decide +kernel

private theorem R06p07_row_03 : pack 32 (R06p07_digit 3)=R06p07_rowCode 3 := by decide +kernel

private theorem R06p07_row_04 : pack 32 (R06p07_digit 4)=R06p07_rowCode 4 := by decide +kernel

private theorem R06p07_row_05 : pack 32 (R06p07_digit 5)=R06p07_rowCode 5 := by decide +kernel

private theorem R06p07_row_06 : pack 32 (R06p07_digit 6)=R06p07_rowCode 6 := by decide +kernel

private theorem R06p07_row_07 : pack 32 (R06p07_digit 7)=R06p07_rowCode 7 := by decide +kernel

private theorem R06p07_row_08 : pack 32 (R06p07_digit 8)=R06p07_rowCode 8 := by decide +kernel

private theorem R06p07_row_09 : pack 32 (R06p07_digit 9)=R06p07_rowCode 9 := by decide +kernel

private theorem R06p07_row_10 : pack 32 (R06p07_digit 10)=R06p07_rowCode 10 := by decide +kernel

private theorem R06p07_row_11 : pack 32 (R06p07_digit 11)=R06p07_rowCode 11 := by decide +kernel

private theorem R06p07_row_12 : pack 32 (R06p07_digit 12)=R06p07_rowCode 12 := by decide +kernel

private theorem R06p07_row_13 : pack 32 (R06p07_digit 13)=R06p07_rowCode 13 := by decide +kernel

private theorem R06p07_row_14 : pack 32 (R06p07_digit 14)=R06p07_rowCode 14 := by decide +kernel

private theorem R06p07_row_15 : pack 32 (R06p07_digit 15)=R06p07_rowCode 15 := by decide +kernel

private theorem R06p07_row_16 : pack 32 (R06p07_digit 16)=R06p07_rowCode 16 := by decide +kernel

private theorem R06p07_row_17 : pack 32 (R06p07_digit 17)=R06p07_rowCode 17 := by decide +kernel

private theorem R06p07_row_18 : pack 32 (R06p07_digit 18)=R06p07_rowCode 18 := by decide +kernel

private theorem R06p07_row_19 : pack 32 (R06p07_digit 19)=R06p07_rowCode 19 := by decide +kernel

private theorem R06p07_row_20 : pack 32 (R06p07_digit 20)=R06p07_rowCode 20 := by decide +kernel

private theorem R06p07_row_21 : pack 32 (R06p07_digit 21)=R06p07_rowCode 21 := by decide +kernel

theorem R06p07_row_binding : ∀ i : Fin 22,pack 32 (R06p07_digit i)=R06p07_rowCode i := by
  intro i
  fin_cases i
  · exact R06p07_row_00
  · exact R06p07_row_01
  · exact R06p07_row_02
  · exact R06p07_row_03
  · exact R06p07_row_04
  · exact R06p07_row_05
  · exact R06p07_row_06
  · exact R06p07_row_07
  · exact R06p07_row_08
  · exact R06p07_row_09
  · exact R06p07_row_10
  · exact R06p07_row_11
  · exact R06p07_row_12
  · exact R06p07_row_13
  · exact R06p07_row_14
  · exact R06p07_row_15
  · exact R06p07_row_16
  · exact R06p07_row_17
  · exact R06p07_row_18
  · exact R06p07_row_19
  · exact R06p07_row_20
  · exact R06p07_row_21

private theorem R06p07_column_00 : reversePack 32 (fun j : Fin 22 => R06p07_digit j 0)=R06p07_columnCode 0 := by decide +kernel

private theorem R06p07_column_01 : reversePack 32 (fun j : Fin 22 => R06p07_digit j 1)=R06p07_columnCode 1 := by decide +kernel

private theorem R06p07_column_02 : reversePack 32 (fun j : Fin 22 => R06p07_digit j 2)=R06p07_columnCode 2 := by decide +kernel

private theorem R06p07_column_03 : reversePack 32 (fun j : Fin 22 => R06p07_digit j 3)=R06p07_columnCode 3 := by decide +kernel

private theorem R06p07_column_04 : reversePack 32 (fun j : Fin 22 => R06p07_digit j 4)=R06p07_columnCode 4 := by decide +kernel

private theorem R06p07_column_05 : reversePack 32 (fun j : Fin 22 => R06p07_digit j 5)=R06p07_columnCode 5 := by decide +kernel

private theorem R06p07_column_06 : reversePack 32 (fun j : Fin 22 => R06p07_digit j 6)=R06p07_columnCode 6 := by decide +kernel

private theorem R06p07_column_07 : reversePack 32 (fun j : Fin 22 => R06p07_digit j 7)=R06p07_columnCode 7 := by decide +kernel

private theorem R06p07_column_08 : reversePack 32 (fun j : Fin 22 => R06p07_digit j 8)=R06p07_columnCode 8 := by decide +kernel

private theorem R06p07_column_09 : reversePack 32 (fun j : Fin 22 => R06p07_digit j 9)=R06p07_columnCode 9 := by decide +kernel

private theorem R06p07_column_10 : reversePack 32 (fun j : Fin 22 => R06p07_digit j 10)=R06p07_columnCode 10 := by decide +kernel

private theorem R06p07_column_11 : reversePack 32 (fun j : Fin 22 => R06p07_digit j 11)=R06p07_columnCode 11 := by decide +kernel

private theorem R06p07_column_12 : reversePack 32 (fun j : Fin 22 => R06p07_digit j 12)=R06p07_columnCode 12 := by decide +kernel

private theorem R06p07_column_13 : reversePack 32 (fun j : Fin 22 => R06p07_digit j 13)=R06p07_columnCode 13 := by decide +kernel

private theorem R06p07_column_14 : reversePack 32 (fun j : Fin 22 => R06p07_digit j 14)=R06p07_columnCode 14 := by decide +kernel

private theorem R06p07_column_15 : reversePack 32 (fun j : Fin 22 => R06p07_digit j 15)=R06p07_columnCode 15 := by decide +kernel

private theorem R06p07_column_16 : reversePack 32 (fun j : Fin 22 => R06p07_digit j 16)=R06p07_columnCode 16 := by decide +kernel

private theorem R06p07_column_17 : reversePack 32 (fun j : Fin 22 => R06p07_digit j 17)=R06p07_columnCode 17 := by decide +kernel

private theorem R06p07_column_18 : reversePack 32 (fun j : Fin 22 => R06p07_digit j 18)=R06p07_columnCode 18 := by decide +kernel

private theorem R06p07_column_19 : reversePack 32 (fun j : Fin 22 => R06p07_digit j 19)=R06p07_columnCode 19 := by decide +kernel

private theorem R06p07_column_20 : reversePack 32 (fun j : Fin 22 => R06p07_digit j 20)=R06p07_columnCode 20 := by decide +kernel

private theorem R06p07_column_21 : reversePack 32 (fun j : Fin 22 => R06p07_digit j 21)=R06p07_columnCode 21 := by decide +kernel

theorem R06p07_column_binding : ∀ i : Fin 22,reversePack 32 (fun j : Fin 22 => R06p07_digit j i)=R06p07_columnCode i := by
  intro i
  fin_cases i
  · exact R06p07_column_00
  · exact R06p07_column_01
  · exact R06p07_column_02
  · exact R06p07_column_03
  · exact R06p07_column_04
  · exact R06p07_column_05
  · exact R06p07_column_06
  · exact R06p07_column_07
  · exact R06p07_column_08
  · exact R06p07_column_09
  · exact R06p07_column_10
  · exact R06p07_column_11
  · exact R06p07_column_12
  · exact R06p07_column_13
  · exact R06p07_column_14
  · exact R06p07_column_15
  · exact R06p07_column_16
  · exact R06p07_column_17
  · exact R06p07_column_18
  · exact R06p07_column_19
  · exact R06p07_column_20
  · exact R06p07_column_21

def R06p07_data : PackedData 22 2 32 where
  raw := R06p07_digit
  digit_lt := R06p07_bound
  rowCode := R06p07_rowCode
  columnCode := R06p07_columnCode
  row_binding := R06p07_row_binding
  column_binding := R06p07_column_binding

def R06e02_lowColumnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 2794064
  | 1 => 2310992
  | 2 => 1921929
  | 3 => 1093758
  | 4 => 979971
  | 5 => 3449090
  | 6 => 267395
  | 7 => 196947
  | 8 => 3448866
  | 9 => 307330
  | 10 => 392128
  | 11 => 566337
  | 12 => 4226
  | 13 => 3539281
  | 14 => 213459
  | 15 => 21200
  | 16 => 4112592
  | 17 => 1004417
  | 18 => 611201
  | 19 => 425984
  | 20 => 1048576
  | 21 => 3035856
  | _ => 0

def R06e02_rowCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 1276626883034186105773622272
  | 1 => 1181744578541369982976
  | 2 => 32768
  | 3 => 33792
  | 4 => 40564820455225577434380029165601
  | 5 => 1099511660544
  | 6 => 40564820455225614589076954972193
  | 7 => 40566097080855351077196699534336
  | 8 => 1276626882999283207620264992
  | 9 => 40566095870747786885160060847137
  | 10 => 36028798093754368
  | 11 => 1125899906842624
  | 12 => 40566095870748939841850114606080
  | 13 => 37190980844158977
  | 14 => 40566097080854198120506647905312
  | 15 => 39615290182988974406790840321
  | 16 => 1276626846105795060167607328
  | 17 => 40604473184330005408353231044641
  | 18 => 40604473183149414949786357859328
  | 19 => 40566097041894709539729187013633
  | 20 => 1267651809190942505372842230784
  | 21 => 40564820416266053951770641563681
  | _ => 0

def R06e02_columnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 38723406312453695945573377
  | 1 => 38723443205940777172598785
  | 2 => 40566057148561264293757604365344
  | 3 => 1308542553855626132573258776608
  | 4 => 41832469807531606314507543020544
  | 5 => 1267650600265122890744707711009
  | 6 => 41832469808712197934090008166400
  | 7 => 41832508530973623268629411790848
  | 8 => 1267651809154049017226463313953
  | 9 => 1267650601408821058499072000000
  | 10 => 38997571055545856589824
  | 11 => 40564819245082308740749268616192
  | 12 => 1267650601408821057398486597632
  | 13 => 40564857930745393867132675063841
  | 14 => 41832508532154214889381182832640
  | 15 => 38724586904108531502284800
  | 16 => 38724585751151843598173217
  | 17 => 40564819208521978913482706289664
  | 18 => 40564819208521978913482705208320
  | 19 => 1074823168
  | 20 => 32
  | 21 => 38724586904108531503367169
  | _ => 0

def R06e02_digit (i j : Fin 22) : ℕ := packedDigit 1 (R06e02_lowColumnCode j) i.val

private theorem R06e02_bound_00 : ∀ j : Fin 22,R06e02_digit 0 j<2 := by decide +kernel

private theorem R06e02_bound_01 : ∀ j : Fin 22,R06e02_digit 1 j<2 := by decide +kernel

private theorem R06e02_bound_02 : ∀ j : Fin 22,R06e02_digit 2 j<2 := by decide +kernel

private theorem R06e02_bound_03 : ∀ j : Fin 22,R06e02_digit 3 j<2 := by decide +kernel

private theorem R06e02_bound_04 : ∀ j : Fin 22,R06e02_digit 4 j<2 := by decide +kernel

private theorem R06e02_bound_05 : ∀ j : Fin 22,R06e02_digit 5 j<2 := by decide +kernel

private theorem R06e02_bound_06 : ∀ j : Fin 22,R06e02_digit 6 j<2 := by decide +kernel

private theorem R06e02_bound_07 : ∀ j : Fin 22,R06e02_digit 7 j<2 := by decide +kernel

private theorem R06e02_bound_08 : ∀ j : Fin 22,R06e02_digit 8 j<2 := by decide +kernel

private theorem R06e02_bound_09 : ∀ j : Fin 22,R06e02_digit 9 j<2 := by decide +kernel

private theorem R06e02_bound_10 : ∀ j : Fin 22,R06e02_digit 10 j<2 := by decide +kernel

private theorem R06e02_bound_11 : ∀ j : Fin 22,R06e02_digit 11 j<2 := by decide +kernel

private theorem R06e02_bound_12 : ∀ j : Fin 22,R06e02_digit 12 j<2 := by decide +kernel

private theorem R06e02_bound_13 : ∀ j : Fin 22,R06e02_digit 13 j<2 := by decide +kernel

private theorem R06e02_bound_14 : ∀ j : Fin 22,R06e02_digit 14 j<2 := by decide +kernel

private theorem R06e02_bound_15 : ∀ j : Fin 22,R06e02_digit 15 j<2 := by decide +kernel

private theorem R06e02_bound_16 : ∀ j : Fin 22,R06e02_digit 16 j<2 := by decide +kernel

private theorem R06e02_bound_17 : ∀ j : Fin 22,R06e02_digit 17 j<2 := by decide +kernel

private theorem R06e02_bound_18 : ∀ j : Fin 22,R06e02_digit 18 j<2 := by decide +kernel

private theorem R06e02_bound_19 : ∀ j : Fin 22,R06e02_digit 19 j<2 := by decide +kernel

private theorem R06e02_bound_20 : ∀ j : Fin 22,R06e02_digit 20 j<2 := by decide +kernel

private theorem R06e02_bound_21 : ∀ j : Fin 22,R06e02_digit 21 j<2 := by decide +kernel

theorem R06e02_bound : ∀ i j : Fin 22,R06e02_digit i j<2 := by
  intro i j
  fin_cases i
  · exact R06e02_bound_00 j
  · exact R06e02_bound_01 j
  · exact R06e02_bound_02 j
  · exact R06e02_bound_03 j
  · exact R06e02_bound_04 j
  · exact R06e02_bound_05 j
  · exact R06e02_bound_06 j
  · exact R06e02_bound_07 j
  · exact R06e02_bound_08 j
  · exact R06e02_bound_09 j
  · exact R06e02_bound_10 j
  · exact R06e02_bound_11 j
  · exact R06e02_bound_12 j
  · exact R06e02_bound_13 j
  · exact R06e02_bound_14 j
  · exact R06e02_bound_15 j
  · exact R06e02_bound_16 j
  · exact R06e02_bound_17 j
  · exact R06e02_bound_18 j
  · exact R06e02_bound_19 j
  · exact R06e02_bound_20 j
  · exact R06e02_bound_21 j

private theorem R06e02_row_00 : pack 32 (R06e02_digit 0)=R06e02_rowCode 0 := by decide +kernel

private theorem R06e02_row_01 : pack 32 (R06e02_digit 1)=R06e02_rowCode 1 := by decide +kernel

private theorem R06e02_row_02 : pack 32 (R06e02_digit 2)=R06e02_rowCode 2 := by decide +kernel

private theorem R06e02_row_03 : pack 32 (R06e02_digit 3)=R06e02_rowCode 3 := by decide +kernel

private theorem R06e02_row_04 : pack 32 (R06e02_digit 4)=R06e02_rowCode 4 := by decide +kernel

private theorem R06e02_row_05 : pack 32 (R06e02_digit 5)=R06e02_rowCode 5 := by decide +kernel

private theorem R06e02_row_06 : pack 32 (R06e02_digit 6)=R06e02_rowCode 6 := by decide +kernel

private theorem R06e02_row_07 : pack 32 (R06e02_digit 7)=R06e02_rowCode 7 := by decide +kernel

private theorem R06e02_row_08 : pack 32 (R06e02_digit 8)=R06e02_rowCode 8 := by decide +kernel

private theorem R06e02_row_09 : pack 32 (R06e02_digit 9)=R06e02_rowCode 9 := by decide +kernel

private theorem R06e02_row_10 : pack 32 (R06e02_digit 10)=R06e02_rowCode 10 := by decide +kernel

private theorem R06e02_row_11 : pack 32 (R06e02_digit 11)=R06e02_rowCode 11 := by decide +kernel

private theorem R06e02_row_12 : pack 32 (R06e02_digit 12)=R06e02_rowCode 12 := by decide +kernel

private theorem R06e02_row_13 : pack 32 (R06e02_digit 13)=R06e02_rowCode 13 := by decide +kernel

private theorem R06e02_row_14 : pack 32 (R06e02_digit 14)=R06e02_rowCode 14 := by decide +kernel

private theorem R06e02_row_15 : pack 32 (R06e02_digit 15)=R06e02_rowCode 15 := by decide +kernel

private theorem R06e02_row_16 : pack 32 (R06e02_digit 16)=R06e02_rowCode 16 := by decide +kernel

private theorem R06e02_row_17 : pack 32 (R06e02_digit 17)=R06e02_rowCode 17 := by decide +kernel

private theorem R06e02_row_18 : pack 32 (R06e02_digit 18)=R06e02_rowCode 18 := by decide +kernel

private theorem R06e02_row_19 : pack 32 (R06e02_digit 19)=R06e02_rowCode 19 := by decide +kernel

private theorem R06e02_row_20 : pack 32 (R06e02_digit 20)=R06e02_rowCode 20 := by decide +kernel

private theorem R06e02_row_21 : pack 32 (R06e02_digit 21)=R06e02_rowCode 21 := by decide +kernel

theorem R06e02_row_binding : ∀ i : Fin 22,pack 32 (R06e02_digit i)=R06e02_rowCode i := by
  intro i
  fin_cases i
  · exact R06e02_row_00
  · exact R06e02_row_01
  · exact R06e02_row_02
  · exact R06e02_row_03
  · exact R06e02_row_04
  · exact R06e02_row_05
  · exact R06e02_row_06
  · exact R06e02_row_07
  · exact R06e02_row_08
  · exact R06e02_row_09
  · exact R06e02_row_10
  · exact R06e02_row_11
  · exact R06e02_row_12
  · exact R06e02_row_13
  · exact R06e02_row_14
  · exact R06e02_row_15
  · exact R06e02_row_16
  · exact R06e02_row_17
  · exact R06e02_row_18
  · exact R06e02_row_19
  · exact R06e02_row_20
  · exact R06e02_row_21

private theorem R06e02_column_00 : reversePack 32 (fun j : Fin 22 => R06e02_digit j 0)=R06e02_columnCode 0 := by decide +kernel

private theorem R06e02_column_01 : reversePack 32 (fun j : Fin 22 => R06e02_digit j 1)=R06e02_columnCode 1 := by decide +kernel

private theorem R06e02_column_02 : reversePack 32 (fun j : Fin 22 => R06e02_digit j 2)=R06e02_columnCode 2 := by decide +kernel

private theorem R06e02_column_03 : reversePack 32 (fun j : Fin 22 => R06e02_digit j 3)=R06e02_columnCode 3 := by decide +kernel

private theorem R06e02_column_04 : reversePack 32 (fun j : Fin 22 => R06e02_digit j 4)=R06e02_columnCode 4 := by decide +kernel

private theorem R06e02_column_05 : reversePack 32 (fun j : Fin 22 => R06e02_digit j 5)=R06e02_columnCode 5 := by decide +kernel

private theorem R06e02_column_06 : reversePack 32 (fun j : Fin 22 => R06e02_digit j 6)=R06e02_columnCode 6 := by decide +kernel

private theorem R06e02_column_07 : reversePack 32 (fun j : Fin 22 => R06e02_digit j 7)=R06e02_columnCode 7 := by decide +kernel

private theorem R06e02_column_08 : reversePack 32 (fun j : Fin 22 => R06e02_digit j 8)=R06e02_columnCode 8 := by decide +kernel

private theorem R06e02_column_09 : reversePack 32 (fun j : Fin 22 => R06e02_digit j 9)=R06e02_columnCode 9 := by decide +kernel

private theorem R06e02_column_10 : reversePack 32 (fun j : Fin 22 => R06e02_digit j 10)=R06e02_columnCode 10 := by decide +kernel

private theorem R06e02_column_11 : reversePack 32 (fun j : Fin 22 => R06e02_digit j 11)=R06e02_columnCode 11 := by decide +kernel

private theorem R06e02_column_12 : reversePack 32 (fun j : Fin 22 => R06e02_digit j 12)=R06e02_columnCode 12 := by decide +kernel

private theorem R06e02_column_13 : reversePack 32 (fun j : Fin 22 => R06e02_digit j 13)=R06e02_columnCode 13 := by decide +kernel

private theorem R06e02_column_14 : reversePack 32 (fun j : Fin 22 => R06e02_digit j 14)=R06e02_columnCode 14 := by decide +kernel

private theorem R06e02_column_15 : reversePack 32 (fun j : Fin 22 => R06e02_digit j 15)=R06e02_columnCode 15 := by decide +kernel

private theorem R06e02_column_16 : reversePack 32 (fun j : Fin 22 => R06e02_digit j 16)=R06e02_columnCode 16 := by decide +kernel

private theorem R06e02_column_17 : reversePack 32 (fun j : Fin 22 => R06e02_digit j 17)=R06e02_columnCode 17 := by decide +kernel

private theorem R06e02_column_18 : reversePack 32 (fun j : Fin 22 => R06e02_digit j 18)=R06e02_columnCode 18 := by decide +kernel

private theorem R06e02_column_19 : reversePack 32 (fun j : Fin 22 => R06e02_digit j 19)=R06e02_columnCode 19 := by decide +kernel

private theorem R06e02_column_20 : reversePack 32 (fun j : Fin 22 => R06e02_digit j 20)=R06e02_columnCode 20 := by decide +kernel

private theorem R06e02_column_21 : reversePack 32 (fun j : Fin 22 => R06e02_digit j 21)=R06e02_columnCode 21 := by decide +kernel

theorem R06e02_column_binding : ∀ i : Fin 22,reversePack 32 (fun j : Fin 22 => R06e02_digit j i)=R06e02_columnCode i := by
  intro i
  fin_cases i
  · exact R06e02_column_00
  · exact R06e02_column_01
  · exact R06e02_column_02
  · exact R06e02_column_03
  · exact R06e02_column_04
  · exact R06e02_column_05
  · exact R06e02_column_06
  · exact R06e02_column_07
  · exact R06e02_column_08
  · exact R06e02_column_09
  · exact R06e02_column_10
  · exact R06e02_column_11
  · exact R06e02_column_12
  · exact R06e02_column_13
  · exact R06e02_column_14
  · exact R06e02_column_15
  · exact R06e02_column_16
  · exact R06e02_column_17
  · exact R06e02_column_18
  · exact R06e02_column_19
  · exact R06e02_column_20
  · exact R06e02_column_21

def R06e02_data : PackedData 22 2 32 where
  raw := R06e02_digit
  digit_lt := R06e02_bound
  rowCode := R06e02_rowCode
  columnCode := R06e02_columnCode
  row_binding := R06e02_row_binding
  column_binding := R06e02_column_binding

def R07p03_lowColumnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 3722514
  | 1 => 3179183
  | 2 => 3152157
  | 3 => 2439732
  | 4 => 3341083
  | 5 => 2828852
  | 6 => 3361328
  | 7 => 61838
  | 8 => 3148336
  | 9 => 1116724
  | 10 => 84528
  | 11 => 1059380
  | 12 => 1407686
  | 13 => 2306724
  | 14 => 2537620
  | 15 => 2959526
  | 16 => 3172916
  | 17 => 3142180
  | 18 => 542866
  | 19 => 3328560
  | 20 => 1231408
  | 21 => 3571716
  | _ => 0

def R07p03_rowCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 1049632
  | 1 => 1237977819370164771028467745
  | 2 => 40564859140852994087999651218464
  | 3 => 34360788000
  | 4 => 1308503831631095376896878216193
  | 5 => 1307304613853271395142738149408
  | 6 => 1152921504606846976
  | 7 => 1237979036855273635857825824
  | 8 => 34360787969
  | 9 => 1307304576075492453690184335392
  | 10 => 1
  | 11 => 1308503869411180161358646772737
  | 12 => 38686844865698537388672000
  | 13 => 39933549653204920777605120
  | 14 => 1308542516077848280771087826945
  | 15 => 41872122575595521707073340440609
  | 16 => 38723443207101828164517888
  | 17 => 41872122575632415195187507101696
  | 18 => 40564857931890244921207273062400
  | 19 => 1276663444444911365684985857
  | 20 => 41872085097715711019403736777761
  | 21 => 40604473222108937272376651973665
  | _ => 0

def R07p03_columnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 1267689285891387712510072194081
  | 1 => 41873323038935551955315143475233
  | 2 => 40605709914262880714331462303777
  | 3 => 39653975810333535247968272385
  | 4 => 41833746433235130869670946537505
  | 5 => 39653975810333500063597200385
  | 6 => 39894553201330201673334817
  | 7 => 1308502622742132095752521908224
  | 8 => 39894553201330167278993441
  | 9 => 39653975810333498964084523040
  | 10 => 39894553201330201672286208
  | 11 => 39653975810333500063562596384
  | 12 => 1307264720446039137690838925344
  | 13 => 39615291364696361931883151361
  | 14 => 39652768063952619832639258625
  | 15 => 1307265891591773932639513248769
  | 16 => 39653975810333500097922334753
  | 17 => 39615290184104741249905361921
  | 18 => 1267689287035049816281971688448
  | 19 => 39894553201330202713522209
  | 20 => 39894553201330202713522208
  | 21 => 39614081257132168797846798369
  | _ => 0

def R07p03_digit (i j : Fin 22) : ℕ := packedDigit 1 (R07p03_lowColumnCode j) i.val

private theorem R07p03_bound_00 : ∀ j : Fin 22,R07p03_digit 0 j<2 := by decide +kernel

private theorem R07p03_bound_01 : ∀ j : Fin 22,R07p03_digit 1 j<2 := by decide +kernel

private theorem R07p03_bound_02 : ∀ j : Fin 22,R07p03_digit 2 j<2 := by decide +kernel

private theorem R07p03_bound_03 : ∀ j : Fin 22,R07p03_digit 3 j<2 := by decide +kernel

private theorem R07p03_bound_04 : ∀ j : Fin 22,R07p03_digit 4 j<2 := by decide +kernel

private theorem R07p03_bound_05 : ∀ j : Fin 22,R07p03_digit 5 j<2 := by decide +kernel

private theorem R07p03_bound_06 : ∀ j : Fin 22,R07p03_digit 6 j<2 := by decide +kernel

private theorem R07p03_bound_07 : ∀ j : Fin 22,R07p03_digit 7 j<2 := by decide +kernel

private theorem R07p03_bound_08 : ∀ j : Fin 22,R07p03_digit 8 j<2 := by decide +kernel

private theorem R07p03_bound_09 : ∀ j : Fin 22,R07p03_digit 9 j<2 := by decide +kernel

private theorem R07p03_bound_10 : ∀ j : Fin 22,R07p03_digit 10 j<2 := by decide +kernel

private theorem R07p03_bound_11 : ∀ j : Fin 22,R07p03_digit 11 j<2 := by decide +kernel

private theorem R07p03_bound_12 : ∀ j : Fin 22,R07p03_digit 12 j<2 := by decide +kernel

private theorem R07p03_bound_13 : ∀ j : Fin 22,R07p03_digit 13 j<2 := by decide +kernel

private theorem R07p03_bound_14 : ∀ j : Fin 22,R07p03_digit 14 j<2 := by decide +kernel

private theorem R07p03_bound_15 : ∀ j : Fin 22,R07p03_digit 15 j<2 := by decide +kernel

private theorem R07p03_bound_16 : ∀ j : Fin 22,R07p03_digit 16 j<2 := by decide +kernel

private theorem R07p03_bound_17 : ∀ j : Fin 22,R07p03_digit 17 j<2 := by decide +kernel

private theorem R07p03_bound_18 : ∀ j : Fin 22,R07p03_digit 18 j<2 := by decide +kernel

private theorem R07p03_bound_19 : ∀ j : Fin 22,R07p03_digit 19 j<2 := by decide +kernel

private theorem R07p03_bound_20 : ∀ j : Fin 22,R07p03_digit 20 j<2 := by decide +kernel

private theorem R07p03_bound_21 : ∀ j : Fin 22,R07p03_digit 21 j<2 := by decide +kernel

theorem R07p03_bound : ∀ i j : Fin 22,R07p03_digit i j<2 := by
  intro i j
  fin_cases i
  · exact R07p03_bound_00 j
  · exact R07p03_bound_01 j
  · exact R07p03_bound_02 j
  · exact R07p03_bound_03 j
  · exact R07p03_bound_04 j
  · exact R07p03_bound_05 j
  · exact R07p03_bound_06 j
  · exact R07p03_bound_07 j
  · exact R07p03_bound_08 j
  · exact R07p03_bound_09 j
  · exact R07p03_bound_10 j
  · exact R07p03_bound_11 j
  · exact R07p03_bound_12 j
  · exact R07p03_bound_13 j
  · exact R07p03_bound_14 j
  · exact R07p03_bound_15 j
  · exact R07p03_bound_16 j
  · exact R07p03_bound_17 j
  · exact R07p03_bound_18 j
  · exact R07p03_bound_19 j
  · exact R07p03_bound_20 j
  · exact R07p03_bound_21 j

private theorem R07p03_row_00 : pack 32 (R07p03_digit 0)=R07p03_rowCode 0 := by decide +kernel

private theorem R07p03_row_01 : pack 32 (R07p03_digit 1)=R07p03_rowCode 1 := by decide +kernel

private theorem R07p03_row_02 : pack 32 (R07p03_digit 2)=R07p03_rowCode 2 := by decide +kernel

private theorem R07p03_row_03 : pack 32 (R07p03_digit 3)=R07p03_rowCode 3 := by decide +kernel

private theorem R07p03_row_04 : pack 32 (R07p03_digit 4)=R07p03_rowCode 4 := by decide +kernel

private theorem R07p03_row_05 : pack 32 (R07p03_digit 5)=R07p03_rowCode 5 := by decide +kernel

private theorem R07p03_row_06 : pack 32 (R07p03_digit 6)=R07p03_rowCode 6 := by decide +kernel

private theorem R07p03_row_07 : pack 32 (R07p03_digit 7)=R07p03_rowCode 7 := by decide +kernel

private theorem R07p03_row_08 : pack 32 (R07p03_digit 8)=R07p03_rowCode 8 := by decide +kernel

private theorem R07p03_row_09 : pack 32 (R07p03_digit 9)=R07p03_rowCode 9 := by decide +kernel

private theorem R07p03_row_10 : pack 32 (R07p03_digit 10)=R07p03_rowCode 10 := by decide +kernel

private theorem R07p03_row_11 : pack 32 (R07p03_digit 11)=R07p03_rowCode 11 := by decide +kernel

private theorem R07p03_row_12 : pack 32 (R07p03_digit 12)=R07p03_rowCode 12 := by decide +kernel

private theorem R07p03_row_13 : pack 32 (R07p03_digit 13)=R07p03_rowCode 13 := by decide +kernel

private theorem R07p03_row_14 : pack 32 (R07p03_digit 14)=R07p03_rowCode 14 := by decide +kernel

private theorem R07p03_row_15 : pack 32 (R07p03_digit 15)=R07p03_rowCode 15 := by decide +kernel

private theorem R07p03_row_16 : pack 32 (R07p03_digit 16)=R07p03_rowCode 16 := by decide +kernel

private theorem R07p03_row_17 : pack 32 (R07p03_digit 17)=R07p03_rowCode 17 := by decide +kernel

private theorem R07p03_row_18 : pack 32 (R07p03_digit 18)=R07p03_rowCode 18 := by decide +kernel

private theorem R07p03_row_19 : pack 32 (R07p03_digit 19)=R07p03_rowCode 19 := by decide +kernel

private theorem R07p03_row_20 : pack 32 (R07p03_digit 20)=R07p03_rowCode 20 := by decide +kernel

private theorem R07p03_row_21 : pack 32 (R07p03_digit 21)=R07p03_rowCode 21 := by decide +kernel

theorem R07p03_row_binding : ∀ i : Fin 22,pack 32 (R07p03_digit i)=R07p03_rowCode i := by
  intro i
  fin_cases i
  · exact R07p03_row_00
  · exact R07p03_row_01
  · exact R07p03_row_02
  · exact R07p03_row_03
  · exact R07p03_row_04
  · exact R07p03_row_05
  · exact R07p03_row_06
  · exact R07p03_row_07
  · exact R07p03_row_08
  · exact R07p03_row_09
  · exact R07p03_row_10
  · exact R07p03_row_11
  · exact R07p03_row_12
  · exact R07p03_row_13
  · exact R07p03_row_14
  · exact R07p03_row_15
  · exact R07p03_row_16
  · exact R07p03_row_17
  · exact R07p03_row_18
  · exact R07p03_row_19
  · exact R07p03_row_20
  · exact R07p03_row_21

private theorem R07p03_column_00 : reversePack 32 (fun j : Fin 22 => R07p03_digit j 0)=R07p03_columnCode 0 := by decide +kernel

private theorem R07p03_column_01 : reversePack 32 (fun j : Fin 22 => R07p03_digit j 1)=R07p03_columnCode 1 := by decide +kernel

private theorem R07p03_column_02 : reversePack 32 (fun j : Fin 22 => R07p03_digit j 2)=R07p03_columnCode 2 := by decide +kernel

private theorem R07p03_column_03 : reversePack 32 (fun j : Fin 22 => R07p03_digit j 3)=R07p03_columnCode 3 := by decide +kernel

private theorem R07p03_column_04 : reversePack 32 (fun j : Fin 22 => R07p03_digit j 4)=R07p03_columnCode 4 := by decide +kernel

private theorem R07p03_column_05 : reversePack 32 (fun j : Fin 22 => R07p03_digit j 5)=R07p03_columnCode 5 := by decide +kernel

private theorem R07p03_column_06 : reversePack 32 (fun j : Fin 22 => R07p03_digit j 6)=R07p03_columnCode 6 := by decide +kernel

private theorem R07p03_column_07 : reversePack 32 (fun j : Fin 22 => R07p03_digit j 7)=R07p03_columnCode 7 := by decide +kernel

private theorem R07p03_column_08 : reversePack 32 (fun j : Fin 22 => R07p03_digit j 8)=R07p03_columnCode 8 := by decide +kernel

private theorem R07p03_column_09 : reversePack 32 (fun j : Fin 22 => R07p03_digit j 9)=R07p03_columnCode 9 := by decide +kernel

private theorem R07p03_column_10 : reversePack 32 (fun j : Fin 22 => R07p03_digit j 10)=R07p03_columnCode 10 := by decide +kernel

private theorem R07p03_column_11 : reversePack 32 (fun j : Fin 22 => R07p03_digit j 11)=R07p03_columnCode 11 := by decide +kernel

private theorem R07p03_column_12 : reversePack 32 (fun j : Fin 22 => R07p03_digit j 12)=R07p03_columnCode 12 := by decide +kernel

private theorem R07p03_column_13 : reversePack 32 (fun j : Fin 22 => R07p03_digit j 13)=R07p03_columnCode 13 := by decide +kernel

private theorem R07p03_column_14 : reversePack 32 (fun j : Fin 22 => R07p03_digit j 14)=R07p03_columnCode 14 := by decide +kernel

private theorem R07p03_column_15 : reversePack 32 (fun j : Fin 22 => R07p03_digit j 15)=R07p03_columnCode 15 := by decide +kernel

private theorem R07p03_column_16 : reversePack 32 (fun j : Fin 22 => R07p03_digit j 16)=R07p03_columnCode 16 := by decide +kernel

private theorem R07p03_column_17 : reversePack 32 (fun j : Fin 22 => R07p03_digit j 17)=R07p03_columnCode 17 := by decide +kernel

private theorem R07p03_column_18 : reversePack 32 (fun j : Fin 22 => R07p03_digit j 18)=R07p03_columnCode 18 := by decide +kernel

private theorem R07p03_column_19 : reversePack 32 (fun j : Fin 22 => R07p03_digit j 19)=R07p03_columnCode 19 := by decide +kernel

private theorem R07p03_column_20 : reversePack 32 (fun j : Fin 22 => R07p03_digit j 20)=R07p03_columnCode 20 := by decide +kernel

private theorem R07p03_column_21 : reversePack 32 (fun j : Fin 22 => R07p03_digit j 21)=R07p03_columnCode 21 := by decide +kernel

theorem R07p03_column_binding : ∀ i : Fin 22,reversePack 32 (fun j : Fin 22 => R07p03_digit j i)=R07p03_columnCode i := by
  intro i
  fin_cases i
  · exact R07p03_column_00
  · exact R07p03_column_01
  · exact R07p03_column_02
  · exact R07p03_column_03
  · exact R07p03_column_04
  · exact R07p03_column_05
  · exact R07p03_column_06
  · exact R07p03_column_07
  · exact R07p03_column_08
  · exact R07p03_column_09
  · exact R07p03_column_10
  · exact R07p03_column_11
  · exact R07p03_column_12
  · exact R07p03_column_13
  · exact R07p03_column_14
  · exact R07p03_column_15
  · exact R07p03_column_16
  · exact R07p03_column_17
  · exact R07p03_column_18
  · exact R07p03_column_19
  · exact R07p03_column_20
  · exact R07p03_column_21

def R07p03_data : PackedData 22 2 32 where
  raw := R07p03_digit
  digit_lt := R07p03_bound
  rowCode := R07p03_rowCode
  columnCode := R07p03_columnCode
  row_binding := R07p03_row_binding
  column_binding := R07p03_column_binding

end SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoCaches04
