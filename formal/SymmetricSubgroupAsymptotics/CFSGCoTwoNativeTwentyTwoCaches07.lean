import SymmetricSubgroupAsymptotics.MatrixKroneckerProductReflection
import Mathlib.Tactic.FinCases

/-! Fixed Co2 binary22 shared caches. Every digit and pack binding is kernel checked. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoCaches07
open MatrixKroneckerProductReflection MatrixKroneckerDotReflection
open MatrixNaturalRowDotReflection SmallNaturalMatrixProductReflection

def R08p02_lowColumnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 1142949
  | 1 => 3271396
  | 2 => 1298432
  | 3 => 400065
  | 4 => 1562088
  | 5 => 3189580
  | 6 => 1477931
  | 7 => 2152648
  | 8 => 1026892
  | 9 => 1392644
  | 10 => 327680
  | 11 => 3162112
  | 12 => 3494784
  | 13 => 1337344
  | 14 => 447136
  | 15 => 3492864
  | 16 => 471184
  | 17 => 230400
  | 18 => 18432
  | 19 => 429568
  | 20 => 1474560
  | 21 => 1220608
  | _ => 0

def R08p02_rowCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 1073774593
  | 1 => 1073741824
  | 2 => 36283917271073
  | 3 => 1134979710976
  | 4 => 1208925819614629174706176
  | 5 => 1180591620718486093857
  | 6 => 1133906001952
  | 7 => 1210107564156885553676321
  | 8 => 1152922605226819584
  | 9 => 39614082438876712118335340576
  | 10 => 39652804662291699888599072768
  | 11 => 40852059112242901311230607392
  | 12 => 1210107564156885553677313
  | 13 => 40564820416266053951770641563681
  | 14 => 1237979036891337617249928225
  | 15 => 41872122575595521708173959365664
  | 16 => 39932332133229408325469217
  | 17 => 41872123784521341322768740811776
  | 18 => 1307265929408752240434114232320
  | 19 => 1099511627776
  | 20 => 41832469845348584585982892835873
  | 21 => 37780120813293180813344
  | _ => 0

def R08p02_columnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 40604434498666884288356137566240
  | 1 => 39615329143629315640012046369
  | 2 => 35219840172064
  | 3 => 40564819246264018414157962444800
  | 4 => 1239187961558030742925115424
  | 5 => 40852059113396948681350971425
  | 6 => 41833708956533605887140699340832
  | 7 => 1237978998810025069184548865
  | 8 => 40852059113396948681385608192
  | 9 => 39614081257132168831165300768
  | 10 => 33587200
  | 11 => 34359738401
  | 12 => 1218638065588202668065
  | 13 => 1127033778241568
  | 14 => 1210107564192070999506944
  | 15 => 37154731319132193
  | 16 => 38686806819325134920253440
  | 17 => 36028798127308800
  | 18 => 1125934266580992
  | 19 => 1190076202607476736
  | 20 => 1074823200
  | 21 => 1100586418208
  | _ => 0

def R08p02_digit (i j : Fin 22) : ℕ := packedDigit 1 (R08p02_lowColumnCode j) i.val

private theorem R08p02_bound_00 : ∀ j : Fin 22,R08p02_digit 0 j<2 := by decide +kernel

private theorem R08p02_bound_01 : ∀ j : Fin 22,R08p02_digit 1 j<2 := by decide +kernel

private theorem R08p02_bound_02 : ∀ j : Fin 22,R08p02_digit 2 j<2 := by decide +kernel

private theorem R08p02_bound_03 : ∀ j : Fin 22,R08p02_digit 3 j<2 := by decide +kernel

private theorem R08p02_bound_04 : ∀ j : Fin 22,R08p02_digit 4 j<2 := by decide +kernel

private theorem R08p02_bound_05 : ∀ j : Fin 22,R08p02_digit 5 j<2 := by decide +kernel

private theorem R08p02_bound_06 : ∀ j : Fin 22,R08p02_digit 6 j<2 := by decide +kernel

private theorem R08p02_bound_07 : ∀ j : Fin 22,R08p02_digit 7 j<2 := by decide +kernel

private theorem R08p02_bound_08 : ∀ j : Fin 22,R08p02_digit 8 j<2 := by decide +kernel

private theorem R08p02_bound_09 : ∀ j : Fin 22,R08p02_digit 9 j<2 := by decide +kernel

private theorem R08p02_bound_10 : ∀ j : Fin 22,R08p02_digit 10 j<2 := by decide +kernel

private theorem R08p02_bound_11 : ∀ j : Fin 22,R08p02_digit 11 j<2 := by decide +kernel

private theorem R08p02_bound_12 : ∀ j : Fin 22,R08p02_digit 12 j<2 := by decide +kernel

private theorem R08p02_bound_13 : ∀ j : Fin 22,R08p02_digit 13 j<2 := by decide +kernel

private theorem R08p02_bound_14 : ∀ j : Fin 22,R08p02_digit 14 j<2 := by decide +kernel

private theorem R08p02_bound_15 : ∀ j : Fin 22,R08p02_digit 15 j<2 := by decide +kernel

private theorem R08p02_bound_16 : ∀ j : Fin 22,R08p02_digit 16 j<2 := by decide +kernel

private theorem R08p02_bound_17 : ∀ j : Fin 22,R08p02_digit 17 j<2 := by decide +kernel

private theorem R08p02_bound_18 : ∀ j : Fin 22,R08p02_digit 18 j<2 := by decide +kernel

private theorem R08p02_bound_19 : ∀ j : Fin 22,R08p02_digit 19 j<2 := by decide +kernel

private theorem R08p02_bound_20 : ∀ j : Fin 22,R08p02_digit 20 j<2 := by decide +kernel

private theorem R08p02_bound_21 : ∀ j : Fin 22,R08p02_digit 21 j<2 := by decide +kernel

theorem R08p02_bound : ∀ i j : Fin 22,R08p02_digit i j<2 := by
  intro i j
  fin_cases i
  · exact R08p02_bound_00 j
  · exact R08p02_bound_01 j
  · exact R08p02_bound_02 j
  · exact R08p02_bound_03 j
  · exact R08p02_bound_04 j
  · exact R08p02_bound_05 j
  · exact R08p02_bound_06 j
  · exact R08p02_bound_07 j
  · exact R08p02_bound_08 j
  · exact R08p02_bound_09 j
  · exact R08p02_bound_10 j
  · exact R08p02_bound_11 j
  · exact R08p02_bound_12 j
  · exact R08p02_bound_13 j
  · exact R08p02_bound_14 j
  · exact R08p02_bound_15 j
  · exact R08p02_bound_16 j
  · exact R08p02_bound_17 j
  · exact R08p02_bound_18 j
  · exact R08p02_bound_19 j
  · exact R08p02_bound_20 j
  · exact R08p02_bound_21 j

private theorem R08p02_row_00 : pack 32 (R08p02_digit 0)=R08p02_rowCode 0 := by decide +kernel

private theorem R08p02_row_01 : pack 32 (R08p02_digit 1)=R08p02_rowCode 1 := by decide +kernel

private theorem R08p02_row_02 : pack 32 (R08p02_digit 2)=R08p02_rowCode 2 := by decide +kernel

private theorem R08p02_row_03 : pack 32 (R08p02_digit 3)=R08p02_rowCode 3 := by decide +kernel

private theorem R08p02_row_04 : pack 32 (R08p02_digit 4)=R08p02_rowCode 4 := by decide +kernel

private theorem R08p02_row_05 : pack 32 (R08p02_digit 5)=R08p02_rowCode 5 := by decide +kernel

private theorem R08p02_row_06 : pack 32 (R08p02_digit 6)=R08p02_rowCode 6 := by decide +kernel

private theorem R08p02_row_07 : pack 32 (R08p02_digit 7)=R08p02_rowCode 7 := by decide +kernel

private theorem R08p02_row_08 : pack 32 (R08p02_digit 8)=R08p02_rowCode 8 := by decide +kernel

private theorem R08p02_row_09 : pack 32 (R08p02_digit 9)=R08p02_rowCode 9 := by decide +kernel

private theorem R08p02_row_10 : pack 32 (R08p02_digit 10)=R08p02_rowCode 10 := by decide +kernel

private theorem R08p02_row_11 : pack 32 (R08p02_digit 11)=R08p02_rowCode 11 := by decide +kernel

private theorem R08p02_row_12 : pack 32 (R08p02_digit 12)=R08p02_rowCode 12 := by decide +kernel

private theorem R08p02_row_13 : pack 32 (R08p02_digit 13)=R08p02_rowCode 13 := by decide +kernel

private theorem R08p02_row_14 : pack 32 (R08p02_digit 14)=R08p02_rowCode 14 := by decide +kernel

private theorem R08p02_row_15 : pack 32 (R08p02_digit 15)=R08p02_rowCode 15 := by decide +kernel

private theorem R08p02_row_16 : pack 32 (R08p02_digit 16)=R08p02_rowCode 16 := by decide +kernel

private theorem R08p02_row_17 : pack 32 (R08p02_digit 17)=R08p02_rowCode 17 := by decide +kernel

private theorem R08p02_row_18 : pack 32 (R08p02_digit 18)=R08p02_rowCode 18 := by decide +kernel

private theorem R08p02_row_19 : pack 32 (R08p02_digit 19)=R08p02_rowCode 19 := by decide +kernel

private theorem R08p02_row_20 : pack 32 (R08p02_digit 20)=R08p02_rowCode 20 := by decide +kernel

private theorem R08p02_row_21 : pack 32 (R08p02_digit 21)=R08p02_rowCode 21 := by decide +kernel

theorem R08p02_row_binding : ∀ i : Fin 22,pack 32 (R08p02_digit i)=R08p02_rowCode i := by
  intro i
  fin_cases i
  · exact R08p02_row_00
  · exact R08p02_row_01
  · exact R08p02_row_02
  · exact R08p02_row_03
  · exact R08p02_row_04
  · exact R08p02_row_05
  · exact R08p02_row_06
  · exact R08p02_row_07
  · exact R08p02_row_08
  · exact R08p02_row_09
  · exact R08p02_row_10
  · exact R08p02_row_11
  · exact R08p02_row_12
  · exact R08p02_row_13
  · exact R08p02_row_14
  · exact R08p02_row_15
  · exact R08p02_row_16
  · exact R08p02_row_17
  · exact R08p02_row_18
  · exact R08p02_row_19
  · exact R08p02_row_20
  · exact R08p02_row_21

private theorem R08p02_column_00 : reversePack 32 (fun j : Fin 22 => R08p02_digit j 0)=R08p02_columnCode 0 := by decide +kernel

private theorem R08p02_column_01 : reversePack 32 (fun j : Fin 22 => R08p02_digit j 1)=R08p02_columnCode 1 := by decide +kernel

private theorem R08p02_column_02 : reversePack 32 (fun j : Fin 22 => R08p02_digit j 2)=R08p02_columnCode 2 := by decide +kernel

private theorem R08p02_column_03 : reversePack 32 (fun j : Fin 22 => R08p02_digit j 3)=R08p02_columnCode 3 := by decide +kernel

private theorem R08p02_column_04 : reversePack 32 (fun j : Fin 22 => R08p02_digit j 4)=R08p02_columnCode 4 := by decide +kernel

private theorem R08p02_column_05 : reversePack 32 (fun j : Fin 22 => R08p02_digit j 5)=R08p02_columnCode 5 := by decide +kernel

private theorem R08p02_column_06 : reversePack 32 (fun j : Fin 22 => R08p02_digit j 6)=R08p02_columnCode 6 := by decide +kernel

private theorem R08p02_column_07 : reversePack 32 (fun j : Fin 22 => R08p02_digit j 7)=R08p02_columnCode 7 := by decide +kernel

private theorem R08p02_column_08 : reversePack 32 (fun j : Fin 22 => R08p02_digit j 8)=R08p02_columnCode 8 := by decide +kernel

private theorem R08p02_column_09 : reversePack 32 (fun j : Fin 22 => R08p02_digit j 9)=R08p02_columnCode 9 := by decide +kernel

private theorem R08p02_column_10 : reversePack 32 (fun j : Fin 22 => R08p02_digit j 10)=R08p02_columnCode 10 := by decide +kernel

private theorem R08p02_column_11 : reversePack 32 (fun j : Fin 22 => R08p02_digit j 11)=R08p02_columnCode 11 := by decide +kernel

private theorem R08p02_column_12 : reversePack 32 (fun j : Fin 22 => R08p02_digit j 12)=R08p02_columnCode 12 := by decide +kernel

private theorem R08p02_column_13 : reversePack 32 (fun j : Fin 22 => R08p02_digit j 13)=R08p02_columnCode 13 := by decide +kernel

private theorem R08p02_column_14 : reversePack 32 (fun j : Fin 22 => R08p02_digit j 14)=R08p02_columnCode 14 := by decide +kernel

private theorem R08p02_column_15 : reversePack 32 (fun j : Fin 22 => R08p02_digit j 15)=R08p02_columnCode 15 := by decide +kernel

private theorem R08p02_column_16 : reversePack 32 (fun j : Fin 22 => R08p02_digit j 16)=R08p02_columnCode 16 := by decide +kernel

private theorem R08p02_column_17 : reversePack 32 (fun j : Fin 22 => R08p02_digit j 17)=R08p02_columnCode 17 := by decide +kernel

private theorem R08p02_column_18 : reversePack 32 (fun j : Fin 22 => R08p02_digit j 18)=R08p02_columnCode 18 := by decide +kernel

private theorem R08p02_column_19 : reversePack 32 (fun j : Fin 22 => R08p02_digit j 19)=R08p02_columnCode 19 := by decide +kernel

private theorem R08p02_column_20 : reversePack 32 (fun j : Fin 22 => R08p02_digit j 20)=R08p02_columnCode 20 := by decide +kernel

private theorem R08p02_column_21 : reversePack 32 (fun j : Fin 22 => R08p02_digit j 21)=R08p02_columnCode 21 := by decide +kernel

theorem R08p02_column_binding : ∀ i : Fin 22,reversePack 32 (fun j : Fin 22 => R08p02_digit j i)=R08p02_columnCode i := by
  intro i
  fin_cases i
  · exact R08p02_column_00
  · exact R08p02_column_01
  · exact R08p02_column_02
  · exact R08p02_column_03
  · exact R08p02_column_04
  · exact R08p02_column_05
  · exact R08p02_column_06
  · exact R08p02_column_07
  · exact R08p02_column_08
  · exact R08p02_column_09
  · exact R08p02_column_10
  · exact R08p02_column_11
  · exact R08p02_column_12
  · exact R08p02_column_13
  · exact R08p02_column_14
  · exact R08p02_column_15
  · exact R08p02_column_16
  · exact R08p02_column_17
  · exact R08p02_column_18
  · exact R08p02_column_19
  · exact R08p02_column_20
  · exact R08p02_column_21

def R08p02_data : PackedData 22 2 32 where
  raw := R08p02_digit
  digit_lt := R08p02_bound
  rowCode := R08p02_rowCode
  columnCode := R08p02_columnCode
  row_binding := R08p02_row_binding
  column_binding := R08p02_column_binding

def R08p03_lowColumnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 3439313
  | 1 => 3594868
  | 2 => 465885
  | 3 => 2634683
  | 4 => 3151613
  | 5 => 907507
  | 6 => 1377067
  | 7 => 1458229
  | 8 => 4085212
  | 9 => 3001207
  | 10 => 382395
  | 11 => 575356
  | 12 => 3003639
  | 13 => 1194427
  | 14 => 578524
  | 15 => 1999414
  | 16 => 1052160
  | 17 => 1520571
  | 18 => 599372
  | 19 => 114320
  | 20 => 1220608
  | 21 => 471184
  | _ => 0

def R08p03_rowCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 38685664275238905363596289
  | 1 => 38723443207101828164517888
  | 2 => 1237978999997850569342452768
  | 3 => 1276626883035313070832387072
  | 4 => 40604472013184307769166668006433
  | 5 => 38723443243130659544268832
  | 6 => 1237941221065987577854559265
  | 7 => 40604471975405339842193755505665
  | 8 => 1276626883035348255203427328
  | 9 => 39654014768738999216576168993
  | 10 => 40853230223427241001891135488
  | 11 => 39615290219845306757771428897
  | 12 => 40604471975405339842193755505697
  | 13 => 41873360514491108954743886610433
  | 14 => 1181781733237220966433
  | 15 => 1307264720446075165353986490400
  | 16 => 40605709914227140147689757344768
  | 17 => 41832508530973623269763248555040
  | 18 => 40564857930709654462709119321121
  | 19 => 1237978999997850535015251968
  | 20 => 1267690532596102036498995478561
  | 21 => 1152957788491644961
  | _ => 0

def R08p03_columnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 40564857931890246083425423360033
  | 1 => 39654013589265397141019328545
  | 2 => 40605709953223557119510676799488
  | 3 => 41833747643341540979082191176705
  | 4 => 40605711162112518148889509888033
  | 5 => 41832509741043142176948290094080
  | 6 => 41833708956534721653947339145248
  | 7 => 40604473183112520299488400670752
  | 8 => 40890745919098253043005686817
  | 9 => 41872123821157729099495304627201
  | 10 => 41833747643340424085310558732288
  | 11 => 40891953665479133276076508160
  | 12 => 41872123822300309248642174190593
  | 13 => 41833747643340389183477492219936
  | 14 => 40890745920215145751666230272
  | 15 => 1307304576038561774561922155552
  | 16 => 1190076201532653600
  | 17 => 41833747643341540979082225811488
  | 18 => 40852059112278930072816059392
  | 19 => 38686808009401337525567488
  | 20 => 1100586418208
  | 21 => 38686806819325134920253440
  | _ => 0

def R08p03_digit (i j : Fin 22) : ℕ := packedDigit 1 (R08p03_lowColumnCode j) i.val

private theorem R08p03_bound_00 : ∀ j : Fin 22,R08p03_digit 0 j<2 := by decide +kernel

private theorem R08p03_bound_01 : ∀ j : Fin 22,R08p03_digit 1 j<2 := by decide +kernel

private theorem R08p03_bound_02 : ∀ j : Fin 22,R08p03_digit 2 j<2 := by decide +kernel

private theorem R08p03_bound_03 : ∀ j : Fin 22,R08p03_digit 3 j<2 := by decide +kernel

private theorem R08p03_bound_04 : ∀ j : Fin 22,R08p03_digit 4 j<2 := by decide +kernel

private theorem R08p03_bound_05 : ∀ j : Fin 22,R08p03_digit 5 j<2 := by decide +kernel

private theorem R08p03_bound_06 : ∀ j : Fin 22,R08p03_digit 6 j<2 := by decide +kernel

private theorem R08p03_bound_07 : ∀ j : Fin 22,R08p03_digit 7 j<2 := by decide +kernel

private theorem R08p03_bound_08 : ∀ j : Fin 22,R08p03_digit 8 j<2 := by decide +kernel

private theorem R08p03_bound_09 : ∀ j : Fin 22,R08p03_digit 9 j<2 := by decide +kernel

private theorem R08p03_bound_10 : ∀ j : Fin 22,R08p03_digit 10 j<2 := by decide +kernel

private theorem R08p03_bound_11 : ∀ j : Fin 22,R08p03_digit 11 j<2 := by decide +kernel

private theorem R08p03_bound_12 : ∀ j : Fin 22,R08p03_digit 12 j<2 := by decide +kernel

private theorem R08p03_bound_13 : ∀ j : Fin 22,R08p03_digit 13 j<2 := by decide +kernel

private theorem R08p03_bound_14 : ∀ j : Fin 22,R08p03_digit 14 j<2 := by decide +kernel

private theorem R08p03_bound_15 : ∀ j : Fin 22,R08p03_digit 15 j<2 := by decide +kernel

private theorem R08p03_bound_16 : ∀ j : Fin 22,R08p03_digit 16 j<2 := by decide +kernel

private theorem R08p03_bound_17 : ∀ j : Fin 22,R08p03_digit 17 j<2 := by decide +kernel

private theorem R08p03_bound_18 : ∀ j : Fin 22,R08p03_digit 18 j<2 := by decide +kernel

private theorem R08p03_bound_19 : ∀ j : Fin 22,R08p03_digit 19 j<2 := by decide +kernel

private theorem R08p03_bound_20 : ∀ j : Fin 22,R08p03_digit 20 j<2 := by decide +kernel

private theorem R08p03_bound_21 : ∀ j : Fin 22,R08p03_digit 21 j<2 := by decide +kernel

theorem R08p03_bound : ∀ i j : Fin 22,R08p03_digit i j<2 := by
  intro i j
  fin_cases i
  · exact R08p03_bound_00 j
  · exact R08p03_bound_01 j
  · exact R08p03_bound_02 j
  · exact R08p03_bound_03 j
  · exact R08p03_bound_04 j
  · exact R08p03_bound_05 j
  · exact R08p03_bound_06 j
  · exact R08p03_bound_07 j
  · exact R08p03_bound_08 j
  · exact R08p03_bound_09 j
  · exact R08p03_bound_10 j
  · exact R08p03_bound_11 j
  · exact R08p03_bound_12 j
  · exact R08p03_bound_13 j
  · exact R08p03_bound_14 j
  · exact R08p03_bound_15 j
  · exact R08p03_bound_16 j
  · exact R08p03_bound_17 j
  · exact R08p03_bound_18 j
  · exact R08p03_bound_19 j
  · exact R08p03_bound_20 j
  · exact R08p03_bound_21 j

private theorem R08p03_row_00 : pack 32 (R08p03_digit 0)=R08p03_rowCode 0 := by decide +kernel

private theorem R08p03_row_01 : pack 32 (R08p03_digit 1)=R08p03_rowCode 1 := by decide +kernel

private theorem R08p03_row_02 : pack 32 (R08p03_digit 2)=R08p03_rowCode 2 := by decide +kernel

private theorem R08p03_row_03 : pack 32 (R08p03_digit 3)=R08p03_rowCode 3 := by decide +kernel

private theorem R08p03_row_04 : pack 32 (R08p03_digit 4)=R08p03_rowCode 4 := by decide +kernel

private theorem R08p03_row_05 : pack 32 (R08p03_digit 5)=R08p03_rowCode 5 := by decide +kernel

private theorem R08p03_row_06 : pack 32 (R08p03_digit 6)=R08p03_rowCode 6 := by decide +kernel

private theorem R08p03_row_07 : pack 32 (R08p03_digit 7)=R08p03_rowCode 7 := by decide +kernel

private theorem R08p03_row_08 : pack 32 (R08p03_digit 8)=R08p03_rowCode 8 := by decide +kernel

private theorem R08p03_row_09 : pack 32 (R08p03_digit 9)=R08p03_rowCode 9 := by decide +kernel

private theorem R08p03_row_10 : pack 32 (R08p03_digit 10)=R08p03_rowCode 10 := by decide +kernel

private theorem R08p03_row_11 : pack 32 (R08p03_digit 11)=R08p03_rowCode 11 := by decide +kernel

private theorem R08p03_row_12 : pack 32 (R08p03_digit 12)=R08p03_rowCode 12 := by decide +kernel

private theorem R08p03_row_13 : pack 32 (R08p03_digit 13)=R08p03_rowCode 13 := by decide +kernel

private theorem R08p03_row_14 : pack 32 (R08p03_digit 14)=R08p03_rowCode 14 := by decide +kernel

private theorem R08p03_row_15 : pack 32 (R08p03_digit 15)=R08p03_rowCode 15 := by decide +kernel

private theorem R08p03_row_16 : pack 32 (R08p03_digit 16)=R08p03_rowCode 16 := by decide +kernel

private theorem R08p03_row_17 : pack 32 (R08p03_digit 17)=R08p03_rowCode 17 := by decide +kernel

private theorem R08p03_row_18 : pack 32 (R08p03_digit 18)=R08p03_rowCode 18 := by decide +kernel

private theorem R08p03_row_19 : pack 32 (R08p03_digit 19)=R08p03_rowCode 19 := by decide +kernel

private theorem R08p03_row_20 : pack 32 (R08p03_digit 20)=R08p03_rowCode 20 := by decide +kernel

private theorem R08p03_row_21 : pack 32 (R08p03_digit 21)=R08p03_rowCode 21 := by decide +kernel

theorem R08p03_row_binding : ∀ i : Fin 22,pack 32 (R08p03_digit i)=R08p03_rowCode i := by
  intro i
  fin_cases i
  · exact R08p03_row_00
  · exact R08p03_row_01
  · exact R08p03_row_02
  · exact R08p03_row_03
  · exact R08p03_row_04
  · exact R08p03_row_05
  · exact R08p03_row_06
  · exact R08p03_row_07
  · exact R08p03_row_08
  · exact R08p03_row_09
  · exact R08p03_row_10
  · exact R08p03_row_11
  · exact R08p03_row_12
  · exact R08p03_row_13
  · exact R08p03_row_14
  · exact R08p03_row_15
  · exact R08p03_row_16
  · exact R08p03_row_17
  · exact R08p03_row_18
  · exact R08p03_row_19
  · exact R08p03_row_20
  · exact R08p03_row_21

private theorem R08p03_column_00 : reversePack 32 (fun j : Fin 22 => R08p03_digit j 0)=R08p03_columnCode 0 := by decide +kernel

private theorem R08p03_column_01 : reversePack 32 (fun j : Fin 22 => R08p03_digit j 1)=R08p03_columnCode 1 := by decide +kernel

private theorem R08p03_column_02 : reversePack 32 (fun j : Fin 22 => R08p03_digit j 2)=R08p03_columnCode 2 := by decide +kernel

private theorem R08p03_column_03 : reversePack 32 (fun j : Fin 22 => R08p03_digit j 3)=R08p03_columnCode 3 := by decide +kernel

private theorem R08p03_column_04 : reversePack 32 (fun j : Fin 22 => R08p03_digit j 4)=R08p03_columnCode 4 := by decide +kernel

private theorem R08p03_column_05 : reversePack 32 (fun j : Fin 22 => R08p03_digit j 5)=R08p03_columnCode 5 := by decide +kernel

private theorem R08p03_column_06 : reversePack 32 (fun j : Fin 22 => R08p03_digit j 6)=R08p03_columnCode 6 := by decide +kernel

private theorem R08p03_column_07 : reversePack 32 (fun j : Fin 22 => R08p03_digit j 7)=R08p03_columnCode 7 := by decide +kernel

private theorem R08p03_column_08 : reversePack 32 (fun j : Fin 22 => R08p03_digit j 8)=R08p03_columnCode 8 := by decide +kernel

private theorem R08p03_column_09 : reversePack 32 (fun j : Fin 22 => R08p03_digit j 9)=R08p03_columnCode 9 := by decide +kernel

private theorem R08p03_column_10 : reversePack 32 (fun j : Fin 22 => R08p03_digit j 10)=R08p03_columnCode 10 := by decide +kernel

private theorem R08p03_column_11 : reversePack 32 (fun j : Fin 22 => R08p03_digit j 11)=R08p03_columnCode 11 := by decide +kernel

private theorem R08p03_column_12 : reversePack 32 (fun j : Fin 22 => R08p03_digit j 12)=R08p03_columnCode 12 := by decide +kernel

private theorem R08p03_column_13 : reversePack 32 (fun j : Fin 22 => R08p03_digit j 13)=R08p03_columnCode 13 := by decide +kernel

private theorem R08p03_column_14 : reversePack 32 (fun j : Fin 22 => R08p03_digit j 14)=R08p03_columnCode 14 := by decide +kernel

private theorem R08p03_column_15 : reversePack 32 (fun j : Fin 22 => R08p03_digit j 15)=R08p03_columnCode 15 := by decide +kernel

private theorem R08p03_column_16 : reversePack 32 (fun j : Fin 22 => R08p03_digit j 16)=R08p03_columnCode 16 := by decide +kernel

private theorem R08p03_column_17 : reversePack 32 (fun j : Fin 22 => R08p03_digit j 17)=R08p03_columnCode 17 := by decide +kernel

private theorem R08p03_column_18 : reversePack 32 (fun j : Fin 22 => R08p03_digit j 18)=R08p03_columnCode 18 := by decide +kernel

private theorem R08p03_column_19 : reversePack 32 (fun j : Fin 22 => R08p03_digit j 19)=R08p03_columnCode 19 := by decide +kernel

private theorem R08p03_column_20 : reversePack 32 (fun j : Fin 22 => R08p03_digit j 20)=R08p03_columnCode 20 := by decide +kernel

private theorem R08p03_column_21 : reversePack 32 (fun j : Fin 22 => R08p03_digit j 21)=R08p03_columnCode 21 := by decide +kernel

theorem R08p03_column_binding : ∀ i : Fin 22,reversePack 32 (fun j : Fin 22 => R08p03_digit j i)=R08p03_columnCode i := by
  intro i
  fin_cases i
  · exact R08p03_column_00
  · exact R08p03_column_01
  · exact R08p03_column_02
  · exact R08p03_column_03
  · exact R08p03_column_04
  · exact R08p03_column_05
  · exact R08p03_column_06
  · exact R08p03_column_07
  · exact R08p03_column_08
  · exact R08p03_column_09
  · exact R08p03_column_10
  · exact R08p03_column_11
  · exact R08p03_column_12
  · exact R08p03_column_13
  · exact R08p03_column_14
  · exact R08p03_column_15
  · exact R08p03_column_16
  · exact R08p03_column_17
  · exact R08p03_column_18
  · exact R08p03_column_19
  · exact R08p03_column_20
  · exact R08p03_column_21

def R08p03_data : PackedData 22 2 32 where
  raw := R08p03_digit
  digit_lt := R08p03_bound
  rowCode := R08p03_rowCode
  columnCode := R08p03_columnCode
  row_binding := R08p03_row_binding
  column_binding := R08p03_column_binding

def R08p04_lowColumnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 1372751
  | 1 => 1463018
  | 2 => 3838907
  | 3 => 1424349
  | 4 => 3184062
  | 5 => 4037369
  | 6 => 1409128
  | 7 => 1458229
  | 8 => 923606
  | 9 => 3001207
  | 10 => 382395
  | 11 => 575356
  | 12 => 3003639
  | 13 => 834524
  | 14 => 578524
  | 15 => 2074727
  | 16 => 953447
  | 17 => 1520571
  | 18 => 599372
  | 19 => 38081
  | 20 => 1220608
  | 21 => 471184
  | _ => 0

def R08p04_rowCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 39654013589265397139978093569
  | 1 => 39932332133229408325469217
  | 2 => 1239187962710953345936293889
  | 3 => 1276626883035311971354313761
  | 4 => 40564857894148243737412734321664
  | 5 => 39932332169257141299840032
  | 6 => 40853269219843122109454778401
  | 7 => 40604471975405339842193755505696
  | 8 => 1276626883035348254130734080
  | 9 => 38686843748842079357273121
  | 10 => 40853230223427241001891135488
  | 11 => 1246741645000918161195008
  | 12 => 40604471975405339842193755505697
  | 13 => 41833746471012908648904276344833
  | 14 => 1181781732137675784225
  | 15 => 1307265929408788268131655123969
  | 16 => 40566095870748939841850147110912
  | 17 => 41832509739862549396245004157984
  | 18 => 40564859139672367565485713162273
  | 19 => 1239187962710953311609029632
  | 20 => 1267689323633388932622923629601
  | 21 => 1152956689013539840
  | _ => 0

def R08p04_columnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 41873321866608072619243962662944
  | 1 => 1268889788154010836798689804320
  | 2 => 41833747643341540977983754339361
  | 3 => 40605709953223557120611261120544
  | 4 => 1308542517294215406178434809889
  | 5 => 40566097080855351077196733121569
  | 6 => 1239186744036857862342869024
  | 7 => 40604473183112520299488400670752
  | 8 => 1307303406109195195735056876544
  | 9 => 41872123821157729099495304627201
  | 10 => 41833747643340424085310558732288
  | 11 => 40891953665479133276076508160
  | 12 => 41872123822300309248642174190593
  | 13 => 40890745920216272716724995072
  | 14 => 40890745920215145751666230272
  | 15 => 41872085135493455022774841017376
  | 16 => 41872085135493491050472314799104
  | 17 => 41833747643341540979082225811488
  | 18 => 40852059112278930072816059392
  | 19 => 40564819246262900395551540379648
  | 20 => 1100586418208
  | 21 => 38686806819325134920253440
  | _ => 0

def R08p04_digit (i j : Fin 22) : ℕ := packedDigit 1 (R08p04_lowColumnCode j) i.val

private theorem R08p04_bound_00 : ∀ j : Fin 22,R08p04_digit 0 j<2 := by decide +kernel

private theorem R08p04_bound_01 : ∀ j : Fin 22,R08p04_digit 1 j<2 := by decide +kernel

private theorem R08p04_bound_02 : ∀ j : Fin 22,R08p04_digit 2 j<2 := by decide +kernel

private theorem R08p04_bound_03 : ∀ j : Fin 22,R08p04_digit 3 j<2 := by decide +kernel

private theorem R08p04_bound_04 : ∀ j : Fin 22,R08p04_digit 4 j<2 := by decide +kernel

private theorem R08p04_bound_05 : ∀ j : Fin 22,R08p04_digit 5 j<2 := by decide +kernel

private theorem R08p04_bound_06 : ∀ j : Fin 22,R08p04_digit 6 j<2 := by decide +kernel

private theorem R08p04_bound_07 : ∀ j : Fin 22,R08p04_digit 7 j<2 := by decide +kernel

private theorem R08p04_bound_08 : ∀ j : Fin 22,R08p04_digit 8 j<2 := by decide +kernel

private theorem R08p04_bound_09 : ∀ j : Fin 22,R08p04_digit 9 j<2 := by decide +kernel

private theorem R08p04_bound_10 : ∀ j : Fin 22,R08p04_digit 10 j<2 := by decide +kernel

private theorem R08p04_bound_11 : ∀ j : Fin 22,R08p04_digit 11 j<2 := by decide +kernel

private theorem R08p04_bound_12 : ∀ j : Fin 22,R08p04_digit 12 j<2 := by decide +kernel

private theorem R08p04_bound_13 : ∀ j : Fin 22,R08p04_digit 13 j<2 := by decide +kernel

private theorem R08p04_bound_14 : ∀ j : Fin 22,R08p04_digit 14 j<2 := by decide +kernel

private theorem R08p04_bound_15 : ∀ j : Fin 22,R08p04_digit 15 j<2 := by decide +kernel

private theorem R08p04_bound_16 : ∀ j : Fin 22,R08p04_digit 16 j<2 := by decide +kernel

private theorem R08p04_bound_17 : ∀ j : Fin 22,R08p04_digit 17 j<2 := by decide +kernel

private theorem R08p04_bound_18 : ∀ j : Fin 22,R08p04_digit 18 j<2 := by decide +kernel

private theorem R08p04_bound_19 : ∀ j : Fin 22,R08p04_digit 19 j<2 := by decide +kernel

private theorem R08p04_bound_20 : ∀ j : Fin 22,R08p04_digit 20 j<2 := by decide +kernel

private theorem R08p04_bound_21 : ∀ j : Fin 22,R08p04_digit 21 j<2 := by decide +kernel

theorem R08p04_bound : ∀ i j : Fin 22,R08p04_digit i j<2 := by
  intro i j
  fin_cases i
  · exact R08p04_bound_00 j
  · exact R08p04_bound_01 j
  · exact R08p04_bound_02 j
  · exact R08p04_bound_03 j
  · exact R08p04_bound_04 j
  · exact R08p04_bound_05 j
  · exact R08p04_bound_06 j
  · exact R08p04_bound_07 j
  · exact R08p04_bound_08 j
  · exact R08p04_bound_09 j
  · exact R08p04_bound_10 j
  · exact R08p04_bound_11 j
  · exact R08p04_bound_12 j
  · exact R08p04_bound_13 j
  · exact R08p04_bound_14 j
  · exact R08p04_bound_15 j
  · exact R08p04_bound_16 j
  · exact R08p04_bound_17 j
  · exact R08p04_bound_18 j
  · exact R08p04_bound_19 j
  · exact R08p04_bound_20 j
  · exact R08p04_bound_21 j

private theorem R08p04_row_00 : pack 32 (R08p04_digit 0)=R08p04_rowCode 0 := by decide +kernel

private theorem R08p04_row_01 : pack 32 (R08p04_digit 1)=R08p04_rowCode 1 := by decide +kernel

private theorem R08p04_row_02 : pack 32 (R08p04_digit 2)=R08p04_rowCode 2 := by decide +kernel

private theorem R08p04_row_03 : pack 32 (R08p04_digit 3)=R08p04_rowCode 3 := by decide +kernel

private theorem R08p04_row_04 : pack 32 (R08p04_digit 4)=R08p04_rowCode 4 := by decide +kernel

private theorem R08p04_row_05 : pack 32 (R08p04_digit 5)=R08p04_rowCode 5 := by decide +kernel

private theorem R08p04_row_06 : pack 32 (R08p04_digit 6)=R08p04_rowCode 6 := by decide +kernel

private theorem R08p04_row_07 : pack 32 (R08p04_digit 7)=R08p04_rowCode 7 := by decide +kernel

private theorem R08p04_row_08 : pack 32 (R08p04_digit 8)=R08p04_rowCode 8 := by decide +kernel

private theorem R08p04_row_09 : pack 32 (R08p04_digit 9)=R08p04_rowCode 9 := by decide +kernel

private theorem R08p04_row_10 : pack 32 (R08p04_digit 10)=R08p04_rowCode 10 := by decide +kernel

private theorem R08p04_row_11 : pack 32 (R08p04_digit 11)=R08p04_rowCode 11 := by decide +kernel

private theorem R08p04_row_12 : pack 32 (R08p04_digit 12)=R08p04_rowCode 12 := by decide +kernel

private theorem R08p04_row_13 : pack 32 (R08p04_digit 13)=R08p04_rowCode 13 := by decide +kernel

private theorem R08p04_row_14 : pack 32 (R08p04_digit 14)=R08p04_rowCode 14 := by decide +kernel

private theorem R08p04_row_15 : pack 32 (R08p04_digit 15)=R08p04_rowCode 15 := by decide +kernel

private theorem R08p04_row_16 : pack 32 (R08p04_digit 16)=R08p04_rowCode 16 := by decide +kernel

private theorem R08p04_row_17 : pack 32 (R08p04_digit 17)=R08p04_rowCode 17 := by decide +kernel

private theorem R08p04_row_18 : pack 32 (R08p04_digit 18)=R08p04_rowCode 18 := by decide +kernel

private theorem R08p04_row_19 : pack 32 (R08p04_digit 19)=R08p04_rowCode 19 := by decide +kernel

private theorem R08p04_row_20 : pack 32 (R08p04_digit 20)=R08p04_rowCode 20 := by decide +kernel

private theorem R08p04_row_21 : pack 32 (R08p04_digit 21)=R08p04_rowCode 21 := by decide +kernel

theorem R08p04_row_binding : ∀ i : Fin 22,pack 32 (R08p04_digit i)=R08p04_rowCode i := by
  intro i
  fin_cases i
  · exact R08p04_row_00
  · exact R08p04_row_01
  · exact R08p04_row_02
  · exact R08p04_row_03
  · exact R08p04_row_04
  · exact R08p04_row_05
  · exact R08p04_row_06
  · exact R08p04_row_07
  · exact R08p04_row_08
  · exact R08p04_row_09
  · exact R08p04_row_10
  · exact R08p04_row_11
  · exact R08p04_row_12
  · exact R08p04_row_13
  · exact R08p04_row_14
  · exact R08p04_row_15
  · exact R08p04_row_16
  · exact R08p04_row_17
  · exact R08p04_row_18
  · exact R08p04_row_19
  · exact R08p04_row_20
  · exact R08p04_row_21

private theorem R08p04_column_00 : reversePack 32 (fun j : Fin 22 => R08p04_digit j 0)=R08p04_columnCode 0 := by decide +kernel

private theorem R08p04_column_01 : reversePack 32 (fun j : Fin 22 => R08p04_digit j 1)=R08p04_columnCode 1 := by decide +kernel

private theorem R08p04_column_02 : reversePack 32 (fun j : Fin 22 => R08p04_digit j 2)=R08p04_columnCode 2 := by decide +kernel

private theorem R08p04_column_03 : reversePack 32 (fun j : Fin 22 => R08p04_digit j 3)=R08p04_columnCode 3 := by decide +kernel

private theorem R08p04_column_04 : reversePack 32 (fun j : Fin 22 => R08p04_digit j 4)=R08p04_columnCode 4 := by decide +kernel

private theorem R08p04_column_05 : reversePack 32 (fun j : Fin 22 => R08p04_digit j 5)=R08p04_columnCode 5 := by decide +kernel

private theorem R08p04_column_06 : reversePack 32 (fun j : Fin 22 => R08p04_digit j 6)=R08p04_columnCode 6 := by decide +kernel

private theorem R08p04_column_07 : reversePack 32 (fun j : Fin 22 => R08p04_digit j 7)=R08p04_columnCode 7 := by decide +kernel

private theorem R08p04_column_08 : reversePack 32 (fun j : Fin 22 => R08p04_digit j 8)=R08p04_columnCode 8 := by decide +kernel

private theorem R08p04_column_09 : reversePack 32 (fun j : Fin 22 => R08p04_digit j 9)=R08p04_columnCode 9 := by decide +kernel

private theorem R08p04_column_10 : reversePack 32 (fun j : Fin 22 => R08p04_digit j 10)=R08p04_columnCode 10 := by decide +kernel

private theorem R08p04_column_11 : reversePack 32 (fun j : Fin 22 => R08p04_digit j 11)=R08p04_columnCode 11 := by decide +kernel

private theorem R08p04_column_12 : reversePack 32 (fun j : Fin 22 => R08p04_digit j 12)=R08p04_columnCode 12 := by decide +kernel

private theorem R08p04_column_13 : reversePack 32 (fun j : Fin 22 => R08p04_digit j 13)=R08p04_columnCode 13 := by decide +kernel

private theorem R08p04_column_14 : reversePack 32 (fun j : Fin 22 => R08p04_digit j 14)=R08p04_columnCode 14 := by decide +kernel

private theorem R08p04_column_15 : reversePack 32 (fun j : Fin 22 => R08p04_digit j 15)=R08p04_columnCode 15 := by decide +kernel

private theorem R08p04_column_16 : reversePack 32 (fun j : Fin 22 => R08p04_digit j 16)=R08p04_columnCode 16 := by decide +kernel

private theorem R08p04_column_17 : reversePack 32 (fun j : Fin 22 => R08p04_digit j 17)=R08p04_columnCode 17 := by decide +kernel

private theorem R08p04_column_18 : reversePack 32 (fun j : Fin 22 => R08p04_digit j 18)=R08p04_columnCode 18 := by decide +kernel

private theorem R08p04_column_19 : reversePack 32 (fun j : Fin 22 => R08p04_digit j 19)=R08p04_columnCode 19 := by decide +kernel

private theorem R08p04_column_20 : reversePack 32 (fun j : Fin 22 => R08p04_digit j 20)=R08p04_columnCode 20 := by decide +kernel

private theorem R08p04_column_21 : reversePack 32 (fun j : Fin 22 => R08p04_digit j 21)=R08p04_columnCode 21 := by decide +kernel

theorem R08p04_column_binding : ∀ i : Fin 22,reversePack 32 (fun j : Fin 22 => R08p04_digit j i)=R08p04_columnCode i := by
  intro i
  fin_cases i
  · exact R08p04_column_00
  · exact R08p04_column_01
  · exact R08p04_column_02
  · exact R08p04_column_03
  · exact R08p04_column_04
  · exact R08p04_column_05
  · exact R08p04_column_06
  · exact R08p04_column_07
  · exact R08p04_column_08
  · exact R08p04_column_09
  · exact R08p04_column_10
  · exact R08p04_column_11
  · exact R08p04_column_12
  · exact R08p04_column_13
  · exact R08p04_column_14
  · exact R08p04_column_15
  · exact R08p04_column_16
  · exact R08p04_column_17
  · exact R08p04_column_18
  · exact R08p04_column_19
  · exact R08p04_column_20
  · exact R08p04_column_21

def R08p04_data : PackedData 22 2 32 where
  raw := R08p04_digit
  digit_lt := R08p04_bound
  rowCode := R08p04_rowCode
  columnCode := R08p04_columnCode
  row_binding := R08p04_row_binding
  column_binding := R08p04_column_binding

def R08p05_lowColumnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 1142949
  | 1 => 1139322
  | 2 => 1298432
  | 3 => 400065
  | 4 => 2848735
  | 5 => 788859
  | 6 => 1550202
  | 7 => 2191834
  | 8 => 950557
  | 9 => 2369631
  | 10 => 361283
  | 11 => 522
  | 12 => 3439057
  | 13 => 1393233
  | 14 => 447136
  | 15 => 3434065
  | 16 => 471184
  | 17 => 1846326
  | 18 => 90705
  | 19 => 500817
  | 20 => 600118
  | 21 => 1220608
  | _ => 0

def R08p05_rowCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 40852059113396983864683954177
  | 1 => 1267689285854494259547059781664
  | 2 => 1267689285854457105914178568193
  | 3 => 36065116370763808
  | 4 => 1308542553893672542259679068192
  | 5 => 1267689287035048690348812402721
  | 6 => 40852059113396982800605806624
  | 7 => 1210107564156885553676289
  | 8 => 1154048539493400576
  | 9 => 1237979035739506794891870240
  | 10 => 39652804662291699888599072768
  | 11 => 1267689285855610026319306326016
  | 12 => 1210107564156885553677313
  | 13 => 41873361761160119900907217354785
  | 14 => 1237979036855273635858875425
  | 15 => 40604433289741065764409178063872
  | 16 => 1308503830487361179280309486625
  | 17 => 40604434498666884253138447008768
  | 18 => 39654014806750507071034130432
  | 19 => 1267689285854457070729840033792
  | 20 => 40564857930746546788638354572321
  | 21 => 37780084819680501432320
  | _ => 0

def R08p05_columnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 40604434498666884288356137566240
  | 1 => 1268928472599646850130041110560
  | 2 => 35219840172064
  | 3 => 40564819246264018414157962444800
  | 4 => 41873360553451821425038363460609
  | 5 => 41833747679938729389433357894656
  | 6 => 1268928472636576367041194262560
  | 7 => 1268927264890159458045462052865
  | 8 => 40605709914262879553248258196480
  | 9 => 41873360552233148456553047687169
  | 10 => 41832469845348548522001500766208
  | 11 => 1268888540268667703276209176576
  | 12 => 40564857931925986650068235616289
  | 13 => 40564857930709653300524255051808
  | 14 => 1210107564192070999506944
  | 15 => 40564857930709689330420752089121
  | 16 => 38686806819325134920253440
  | 17 => 1307304576037446008852677952544
  | 18 => 40564857930709653301623766646784
  | 19 => 40564857930708536408882893848576
  | 20 => 1307304576037409980055692510208
  | 21 => 1100586418208
  | _ => 0

def R08p05_digit (i j : Fin 22) : ℕ := packedDigit 1 (R08p05_lowColumnCode j) i.val

private theorem R08p05_bound_00 : ∀ j : Fin 22,R08p05_digit 0 j<2 := by decide +kernel

private theorem R08p05_bound_01 : ∀ j : Fin 22,R08p05_digit 1 j<2 := by decide +kernel

private theorem R08p05_bound_02 : ∀ j : Fin 22,R08p05_digit 2 j<2 := by decide +kernel

private theorem R08p05_bound_03 : ∀ j : Fin 22,R08p05_digit 3 j<2 := by decide +kernel

private theorem R08p05_bound_04 : ∀ j : Fin 22,R08p05_digit 4 j<2 := by decide +kernel

private theorem R08p05_bound_05 : ∀ j : Fin 22,R08p05_digit 5 j<2 := by decide +kernel

private theorem R08p05_bound_06 : ∀ j : Fin 22,R08p05_digit 6 j<2 := by decide +kernel

private theorem R08p05_bound_07 : ∀ j : Fin 22,R08p05_digit 7 j<2 := by decide +kernel

private theorem R08p05_bound_08 : ∀ j : Fin 22,R08p05_digit 8 j<2 := by decide +kernel

private theorem R08p05_bound_09 : ∀ j : Fin 22,R08p05_digit 9 j<2 := by decide +kernel

private theorem R08p05_bound_10 : ∀ j : Fin 22,R08p05_digit 10 j<2 := by decide +kernel

private theorem R08p05_bound_11 : ∀ j : Fin 22,R08p05_digit 11 j<2 := by decide +kernel

private theorem R08p05_bound_12 : ∀ j : Fin 22,R08p05_digit 12 j<2 := by decide +kernel

private theorem R08p05_bound_13 : ∀ j : Fin 22,R08p05_digit 13 j<2 := by decide +kernel

private theorem R08p05_bound_14 : ∀ j : Fin 22,R08p05_digit 14 j<2 := by decide +kernel

private theorem R08p05_bound_15 : ∀ j : Fin 22,R08p05_digit 15 j<2 := by decide +kernel

private theorem R08p05_bound_16 : ∀ j : Fin 22,R08p05_digit 16 j<2 := by decide +kernel

private theorem R08p05_bound_17 : ∀ j : Fin 22,R08p05_digit 17 j<2 := by decide +kernel

private theorem R08p05_bound_18 : ∀ j : Fin 22,R08p05_digit 18 j<2 := by decide +kernel

private theorem R08p05_bound_19 : ∀ j : Fin 22,R08p05_digit 19 j<2 := by decide +kernel

private theorem R08p05_bound_20 : ∀ j : Fin 22,R08p05_digit 20 j<2 := by decide +kernel

private theorem R08p05_bound_21 : ∀ j : Fin 22,R08p05_digit 21 j<2 := by decide +kernel

theorem R08p05_bound : ∀ i j : Fin 22,R08p05_digit i j<2 := by
  intro i j
  fin_cases i
  · exact R08p05_bound_00 j
  · exact R08p05_bound_01 j
  · exact R08p05_bound_02 j
  · exact R08p05_bound_03 j
  · exact R08p05_bound_04 j
  · exact R08p05_bound_05 j
  · exact R08p05_bound_06 j
  · exact R08p05_bound_07 j
  · exact R08p05_bound_08 j
  · exact R08p05_bound_09 j
  · exact R08p05_bound_10 j
  · exact R08p05_bound_11 j
  · exact R08p05_bound_12 j
  · exact R08p05_bound_13 j
  · exact R08p05_bound_14 j
  · exact R08p05_bound_15 j
  · exact R08p05_bound_16 j
  · exact R08p05_bound_17 j
  · exact R08p05_bound_18 j
  · exact R08p05_bound_19 j
  · exact R08p05_bound_20 j
  · exact R08p05_bound_21 j

private theorem R08p05_row_00 : pack 32 (R08p05_digit 0)=R08p05_rowCode 0 := by decide +kernel

private theorem R08p05_row_01 : pack 32 (R08p05_digit 1)=R08p05_rowCode 1 := by decide +kernel

private theorem R08p05_row_02 : pack 32 (R08p05_digit 2)=R08p05_rowCode 2 := by decide +kernel

private theorem R08p05_row_03 : pack 32 (R08p05_digit 3)=R08p05_rowCode 3 := by decide +kernel

private theorem R08p05_row_04 : pack 32 (R08p05_digit 4)=R08p05_rowCode 4 := by decide +kernel

private theorem R08p05_row_05 : pack 32 (R08p05_digit 5)=R08p05_rowCode 5 := by decide +kernel

private theorem R08p05_row_06 : pack 32 (R08p05_digit 6)=R08p05_rowCode 6 := by decide +kernel

private theorem R08p05_row_07 : pack 32 (R08p05_digit 7)=R08p05_rowCode 7 := by decide +kernel

private theorem R08p05_row_08 : pack 32 (R08p05_digit 8)=R08p05_rowCode 8 := by decide +kernel

private theorem R08p05_row_09 : pack 32 (R08p05_digit 9)=R08p05_rowCode 9 := by decide +kernel

private theorem R08p05_row_10 : pack 32 (R08p05_digit 10)=R08p05_rowCode 10 := by decide +kernel

private theorem R08p05_row_11 : pack 32 (R08p05_digit 11)=R08p05_rowCode 11 := by decide +kernel

private theorem R08p05_row_12 : pack 32 (R08p05_digit 12)=R08p05_rowCode 12 := by decide +kernel

private theorem R08p05_row_13 : pack 32 (R08p05_digit 13)=R08p05_rowCode 13 := by decide +kernel

private theorem R08p05_row_14 : pack 32 (R08p05_digit 14)=R08p05_rowCode 14 := by decide +kernel

private theorem R08p05_row_15 : pack 32 (R08p05_digit 15)=R08p05_rowCode 15 := by decide +kernel

private theorem R08p05_row_16 : pack 32 (R08p05_digit 16)=R08p05_rowCode 16 := by decide +kernel

private theorem R08p05_row_17 : pack 32 (R08p05_digit 17)=R08p05_rowCode 17 := by decide +kernel

private theorem R08p05_row_18 : pack 32 (R08p05_digit 18)=R08p05_rowCode 18 := by decide +kernel

private theorem R08p05_row_19 : pack 32 (R08p05_digit 19)=R08p05_rowCode 19 := by decide +kernel

private theorem R08p05_row_20 : pack 32 (R08p05_digit 20)=R08p05_rowCode 20 := by decide +kernel

private theorem R08p05_row_21 : pack 32 (R08p05_digit 21)=R08p05_rowCode 21 := by decide +kernel

theorem R08p05_row_binding : ∀ i : Fin 22,pack 32 (R08p05_digit i)=R08p05_rowCode i := by
  intro i
  fin_cases i
  · exact R08p05_row_00
  · exact R08p05_row_01
  · exact R08p05_row_02
  · exact R08p05_row_03
  · exact R08p05_row_04
  · exact R08p05_row_05
  · exact R08p05_row_06
  · exact R08p05_row_07
  · exact R08p05_row_08
  · exact R08p05_row_09
  · exact R08p05_row_10
  · exact R08p05_row_11
  · exact R08p05_row_12
  · exact R08p05_row_13
  · exact R08p05_row_14
  · exact R08p05_row_15
  · exact R08p05_row_16
  · exact R08p05_row_17
  · exact R08p05_row_18
  · exact R08p05_row_19
  · exact R08p05_row_20
  · exact R08p05_row_21

private theorem R08p05_column_00 : reversePack 32 (fun j : Fin 22 => R08p05_digit j 0)=R08p05_columnCode 0 := by decide +kernel

private theorem R08p05_column_01 : reversePack 32 (fun j : Fin 22 => R08p05_digit j 1)=R08p05_columnCode 1 := by decide +kernel

private theorem R08p05_column_02 : reversePack 32 (fun j : Fin 22 => R08p05_digit j 2)=R08p05_columnCode 2 := by decide +kernel

private theorem R08p05_column_03 : reversePack 32 (fun j : Fin 22 => R08p05_digit j 3)=R08p05_columnCode 3 := by decide +kernel

private theorem R08p05_column_04 : reversePack 32 (fun j : Fin 22 => R08p05_digit j 4)=R08p05_columnCode 4 := by decide +kernel

private theorem R08p05_column_05 : reversePack 32 (fun j : Fin 22 => R08p05_digit j 5)=R08p05_columnCode 5 := by decide +kernel

private theorem R08p05_column_06 : reversePack 32 (fun j : Fin 22 => R08p05_digit j 6)=R08p05_columnCode 6 := by decide +kernel

private theorem R08p05_column_07 : reversePack 32 (fun j : Fin 22 => R08p05_digit j 7)=R08p05_columnCode 7 := by decide +kernel

private theorem R08p05_column_08 : reversePack 32 (fun j : Fin 22 => R08p05_digit j 8)=R08p05_columnCode 8 := by decide +kernel

private theorem R08p05_column_09 : reversePack 32 (fun j : Fin 22 => R08p05_digit j 9)=R08p05_columnCode 9 := by decide +kernel

private theorem R08p05_column_10 : reversePack 32 (fun j : Fin 22 => R08p05_digit j 10)=R08p05_columnCode 10 := by decide +kernel

private theorem R08p05_column_11 : reversePack 32 (fun j : Fin 22 => R08p05_digit j 11)=R08p05_columnCode 11 := by decide +kernel

private theorem R08p05_column_12 : reversePack 32 (fun j : Fin 22 => R08p05_digit j 12)=R08p05_columnCode 12 := by decide +kernel

private theorem R08p05_column_13 : reversePack 32 (fun j : Fin 22 => R08p05_digit j 13)=R08p05_columnCode 13 := by decide +kernel

private theorem R08p05_column_14 : reversePack 32 (fun j : Fin 22 => R08p05_digit j 14)=R08p05_columnCode 14 := by decide +kernel

private theorem R08p05_column_15 : reversePack 32 (fun j : Fin 22 => R08p05_digit j 15)=R08p05_columnCode 15 := by decide +kernel

private theorem R08p05_column_16 : reversePack 32 (fun j : Fin 22 => R08p05_digit j 16)=R08p05_columnCode 16 := by decide +kernel

private theorem R08p05_column_17 : reversePack 32 (fun j : Fin 22 => R08p05_digit j 17)=R08p05_columnCode 17 := by decide +kernel

private theorem R08p05_column_18 : reversePack 32 (fun j : Fin 22 => R08p05_digit j 18)=R08p05_columnCode 18 := by decide +kernel

private theorem R08p05_column_19 : reversePack 32 (fun j : Fin 22 => R08p05_digit j 19)=R08p05_columnCode 19 := by decide +kernel

private theorem R08p05_column_20 : reversePack 32 (fun j : Fin 22 => R08p05_digit j 20)=R08p05_columnCode 20 := by decide +kernel

private theorem R08p05_column_21 : reversePack 32 (fun j : Fin 22 => R08p05_digit j 21)=R08p05_columnCode 21 := by decide +kernel

theorem R08p05_column_binding : ∀ i : Fin 22,reversePack 32 (fun j : Fin 22 => R08p05_digit j i)=R08p05_columnCode i := by
  intro i
  fin_cases i
  · exact R08p05_column_00
  · exact R08p05_column_01
  · exact R08p05_column_02
  · exact R08p05_column_03
  · exact R08p05_column_04
  · exact R08p05_column_05
  · exact R08p05_column_06
  · exact R08p05_column_07
  · exact R08p05_column_08
  · exact R08p05_column_09
  · exact R08p05_column_10
  · exact R08p05_column_11
  · exact R08p05_column_12
  · exact R08p05_column_13
  · exact R08p05_column_14
  · exact R08p05_column_15
  · exact R08p05_column_16
  · exact R08p05_column_17
  · exact R08p05_column_18
  · exact R08p05_column_19
  · exact R08p05_column_20
  · exact R08p05_column_21

def R08p05_data : PackedData 22 2 32 where
  raw := R08p05_digit
  digit_lt := R08p05_bound
  rowCode := R08p05_rowCode
  columnCode := R08p05_columnCode
  row_binding := R08p05_row_binding
  column_binding := R08p05_column_binding

end SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoCaches07
