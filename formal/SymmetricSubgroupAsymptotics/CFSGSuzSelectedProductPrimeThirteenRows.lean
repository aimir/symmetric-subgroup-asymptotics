import SymmetricSubgroupAsymptotics.MatrixModelSelectedProductPrimePeriod
import SymmetricSubgroupAsymptotics.CFSGSuzPackedRows00To07
import SymmetricSubgroupAsymptotics.CFSGSuzPackedRows08To15
import SymmetricSubgroupAsymptotics.CFSGSuzPackedRows16To23
import SymmetricSubgroupAsymptotics.CFSGSuzPackedRows24To31
import SymmetricSubgroupAsymptotics.CFSGSuzPackedRows32To39
import SymmetricSubgroupAsymptotics.CFSGSuzPackedRows40To47
import SymmetricSubgroupAsymptotics.CFSGSuzPackedRows48To55
import SymmetricSubgroupAsymptotics.CFSGSuzPackedRows56To63
import Mathlib.Tactic.FinCases

/-! Exact row-code bindings for the two original Suz matrices.
The first matrix reuses its already checked row certificates.
Each new second-row command checks just64 literal coefficients. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSuzSelectedProductPrimeThirteenRows
open MatrixNaturalRowDotReflection
open CFSG.Models.MatrixGroups.Suz

def firstRowCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 224175358324649771740101499125688861058
  | 1 => 109460313688681530642593467373530915841
  | 2 => 107176261372582747393498944450498674978
  | 3 => 14052973723631873697457771095608863237
  | 4 => 172179200654476029832166533818843551781
  | 5 => 11395278430350954787518086918155359761
  | 6 => 129021520366080125607798616011679352196
  | 7 => 120487777413882895149552661626385107301
  | 8 => 129736075554941489266497194452307216745
  | 9 => 85507116931633720968544044335052753442
  | 10 => 177328836532026486826103373647525816336
  | 11 => 49734509929504320121583033391257096857
  | 12 => 86932446285829436303378915427910043716
  | 13 => 177339836981046364127331832095973070489
  | 14 => 24391514991862980774886526162270593601
  | 15 => 50928989934656790392912064749035477673
  | 16 => 182795269034325170931998230178779505152
  | 17 => 5442939718050333552495824580377838596
  | 18 => 120176446751434043391944377530008510725
  | 19 => 129710552858962113880685977887832037728
  | 20 => 199738605966114068192569866410672916866
  | 21 => 120099796586372996810380123593128958289
  | 22 => 135634995084821172876916866345901032980
  | 23 => 8392097335941017331647094860034971216
  | 24 => 138951149089242306878984097064630358570
  | 25 => 119057303318170641397082676549160053252
  | 26 => 139658560118286466503426823250830316705
  | 27 => 182153025179921017829251722741765120342
  | 28 => 120162190367628245582959283601884715544
  | 29 => 85434240465712327571672143786471494016
  | 30 => 11104498287148025097498779300212531562
  | 31 => 91888454522703128118981054971660211848
  | 32 => 28666699042998857521085627646798301841
  | 33 => 128376140395730705106344489528403050838
  | 34 => 53633269556015487203635710010111709314
  | 35 => 175916479369254849034347331861240947220
  | 36 => 177667956034682880575216110747345627156
  | 37 => 85264369958735234239493645500223422744
  | 38 => 34695421480660704541461701443871316368
  | 39 => 6818913573914840298740104864329650198
  | 40 => 32675795040199104944890921240003741701
  | 41 => 134293566794068582671784879806969326177
  | 42 => 2873006674020942181203970217219479908
  | 43 => 23041021566558692328970878032302672512
  | 44 => 107025096677211288916596524148772051242
  | 45 => 54054508580985623439766439695855141136
  | 46 => 197084742660698203289685778759432540257
  | 47 => 96164346616028464178554530496345365136
  | 48 => 29609823763203144734143640774359138320
  | 49 => 42630738092532343937714142329550744069
  | 50 => 177148219808756567927639996641231340561
  | 51 => 181628010330640120878263564927055012996
  | 52 => 182616338899909672796331191754262087705
  | 53 => 203873452481366437324972755038186940056
  | 54 => 221410091719518872630826860154679026769
  | 55 => 33978523220859169728754365328598929750
  | 56 => 177209715162385184783389887427234563097
  | 57 => 22043110771996480366017387802699260996
  | 58 => 34115340364348796625874625347871655522
  | 59 => 43907816864167340135372978106565402949
  | 60 => 135623443345146820484561721736019872408
  | 61 => 506654919132952627441224068555679812
  | 62 => 85906967344342621358676016070559557972
  | 63 => 48621431257333559251792067819928117601
  | _ => 0

def secondRowCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 1
  | 1 => 16
  | 2 => 42
  | 3 => 256
  | 4 => 4096
  | 5 => 16384
  | 6 => 64
  | 7 => 1048576
  | 8 => 4194304
  | 9 => 16777216
  | 10 => 1024
  | 11 => 1073741824
  | 12 => 17179869184
  | 13 => 68719476736
  | 14 => 274877906944
  | 15 => 65536
  | 16 => 4398046511104
  | 17 => 262144
  | 18 => 281474976710656
  | 19 => 4503599627370496
  | 20 => 18014398509481984
  | 21 => 288230376151711744
  | 22 => 1152921504606846976
  | 23 => 4611686018427387904
  | 24 => 67108864
  | 25 => 73786976294838206464
  | 26 => 268435456
  | 27 => 4722366482869645213696
  | 28 => 18889465931478580854784
  | 29 => 4294967296
  | 30 => 1208925819614629174706176
  | 31 => 19342813113834066795298816
  | 32 => 77371252455336267181195264
  | 33 => 1237940039285380274899124224
  | 34 => 4951760157141521099596496896
  | 35 => 19807040628566084398385987584
  | 36 => 1099511627776
  | 37 => 1267650600228229401496703205376
  | 38 => 5070602400912917605986812821504
  | 39 => 20282409603651670423947251286016
  | 40 => 17592186044416
  | 41 => 324518553658426726783156020576256
  | 42 => 70368744177664
  | 43 => 20769187434139310514121985316880384
  | 44 => 83076749736557242056487941267521536
  | 45 => 1125899906842624
  | 46 => 5316911983139663491615228241121378304
  | 47 => 10633824015838039717905506018625218176
  | 48 => 21267647932558653966460912964485513216
  | 49 => 85070591730234615865843651857942052864
  | 50 => 72057594037927936
  | 51 => 91895391009243641019900581553410975314
  | 52 => 53887139206728940707017221582099162146
  | 53 => 13425112756874628287712563313090380200
  | 54 => 199495833801776259576672001949842285830
  | 55 => 133007368376081242872665158676619745364
  | 56 => 5446740987547845553140463089038485121
  | 57 => 18446744073709551616
  | 58 => 11181795431380695924786421730216864330
  | 59 => 3521698974207274162099206828650403176
  | 60 => 184292796868067179089910781121716065634
  | 61 => 295147905179352825856
  | 62 => 172911598559323331016591904474377902213
  | 63 => 192085170650577243846867936810054527257
  | _ => 0

theorem first_row_binding (i j : Fin 64) :
    rawDigit rows1 i.val j.val=packedDigit 2 (firstRowCode i.val) j.val := by
  fin_cases i
  · exact (CFSGSuzPackedRowZeroPilot.raw_row_binding j).trans (CFSGSuzPackedRowZeroPilot.packed_row_binding j).symm
  · exact (CFSGSuzPackedRows00To07.raw_row_01_binding j).trans (CFSGSuzPackedRows00To07.packed_row_01_binding j).symm
  · exact (CFSGSuzPackedRows00To07.raw_row_02_binding j).trans (CFSGSuzPackedRows00To07.packed_row_02_binding j).symm
  · exact (CFSGSuzPackedRows00To07.raw_row_03_binding j).trans (CFSGSuzPackedRows00To07.packed_row_03_binding j).symm
  · exact (CFSGSuzPackedRows00To07.raw_row_04_binding j).trans (CFSGSuzPackedRows00To07.packed_row_04_binding j).symm
  · exact (CFSGSuzPackedRows00To07.raw_row_05_binding j).trans (CFSGSuzPackedRows00To07.packed_row_05_binding j).symm
  · exact (CFSGSuzPackedRows00To07.raw_row_06_binding j).trans (CFSGSuzPackedRows00To07.packed_row_06_binding j).symm
  · exact (CFSGSuzPackedRows00To07.raw_row_07_binding j).trans (CFSGSuzPackedRows00To07.packed_row_07_binding j).symm
  · exact (CFSGSuzPackedRows08To15.raw_row_08_binding j).trans (CFSGSuzPackedRows08To15.packed_row_08_binding j).symm
  · exact (CFSGSuzPackedRows08To15.raw_row_09_binding j).trans (CFSGSuzPackedRows08To15.packed_row_09_binding j).symm
  · exact (CFSGSuzPackedRows08To15.raw_row_10_binding j).trans (CFSGSuzPackedRows08To15.packed_row_10_binding j).symm
  · exact (CFSGSuzPackedRows08To15.raw_row_11_binding j).trans (CFSGSuzPackedRows08To15.packed_row_11_binding j).symm
  · exact (CFSGSuzPackedRows08To15.raw_row_12_binding j).trans (CFSGSuzPackedRows08To15.packed_row_12_binding j).symm
  · exact (CFSGSuzPackedRows08To15.raw_row_13_binding j).trans (CFSGSuzPackedRows08To15.packed_row_13_binding j).symm
  · exact (CFSGSuzPackedRows08To15.raw_row_14_binding j).trans (CFSGSuzPackedRows08To15.packed_row_14_binding j).symm
  · exact (CFSGSuzPackedRows08To15.raw_row_15_binding j).trans (CFSGSuzPackedRows08To15.packed_row_15_binding j).symm
  · exact (CFSGSuzPackedRows16To23.raw_row_16_binding j).trans (CFSGSuzPackedRows16To23.packed_row_16_binding j).symm
  · exact (CFSGSuzPackedRows16To23.raw_row_17_binding j).trans (CFSGSuzPackedRows16To23.packed_row_17_binding j).symm
  · exact (CFSGSuzPackedRows16To23.raw_row_18_binding j).trans (CFSGSuzPackedRows16To23.packed_row_18_binding j).symm
  · exact (CFSGSuzPackedRows16To23.raw_row_19_binding j).trans (CFSGSuzPackedRows16To23.packed_row_19_binding j).symm
  · exact (CFSGSuzPackedRows16To23.raw_row_20_binding j).trans (CFSGSuzPackedRows16To23.packed_row_20_binding j).symm
  · exact (CFSGSuzPackedRows16To23.raw_row_21_binding j).trans (CFSGSuzPackedRows16To23.packed_row_21_binding j).symm
  · exact (CFSGSuzPackedRows16To23.raw_row_22_binding j).trans (CFSGSuzPackedRows16To23.packed_row_22_binding j).symm
  · exact (CFSGSuzPackedRows16To23.raw_row_23_binding j).trans (CFSGSuzPackedRows16To23.packed_row_23_binding j).symm
  · exact (CFSGSuzPackedRows24To31.raw_row_24_binding j).trans (CFSGSuzPackedRows24To31.packed_row_24_binding j).symm
  · exact (CFSGSuzPackedRows24To31.raw_row_25_binding j).trans (CFSGSuzPackedRows24To31.packed_row_25_binding j).symm
  · exact (CFSGSuzPackedRows24To31.raw_row_26_binding j).trans (CFSGSuzPackedRows24To31.packed_row_26_binding j).symm
  · exact (CFSGSuzPackedRows24To31.raw_row_27_binding j).trans (CFSGSuzPackedRows24To31.packed_row_27_binding j).symm
  · exact (CFSGSuzPackedRows24To31.raw_row_28_binding j).trans (CFSGSuzPackedRows24To31.packed_row_28_binding j).symm
  · exact (CFSGSuzPackedRows24To31.raw_row_29_binding j).trans (CFSGSuzPackedRows24To31.packed_row_29_binding j).symm
  · exact (CFSGSuzPackedRows24To31.raw_row_30_binding j).trans (CFSGSuzPackedRows24To31.packed_row_30_binding j).symm
  · exact (CFSGSuzPackedRows24To31.raw_row_31_binding j).trans (CFSGSuzPackedRows24To31.packed_row_31_binding j).symm
  · exact (CFSGSuzPackedRows32To39.raw_row_32_binding j).trans (CFSGSuzPackedRows32To39.packed_row_32_binding j).symm
  · exact (CFSGSuzPackedRows32To39.raw_row_33_binding j).trans (CFSGSuzPackedRows32To39.packed_row_33_binding j).symm
  · exact (CFSGSuzPackedRows32To39.raw_row_34_binding j).trans (CFSGSuzPackedRows32To39.packed_row_34_binding j).symm
  · exact (CFSGSuzPackedRows32To39.raw_row_35_binding j).trans (CFSGSuzPackedRows32To39.packed_row_35_binding j).symm
  · exact (CFSGSuzPackedRows32To39.raw_row_36_binding j).trans (CFSGSuzPackedRows32To39.packed_row_36_binding j).symm
  · exact (CFSGSuzPackedRows32To39.raw_row_37_binding j).trans (CFSGSuzPackedRows32To39.packed_row_37_binding j).symm
  · exact (CFSGSuzPackedRows32To39.raw_row_38_binding j).trans (CFSGSuzPackedRows32To39.packed_row_38_binding j).symm
  · exact (CFSGSuzPackedRows32To39.raw_row_39_binding j).trans (CFSGSuzPackedRows32To39.packed_row_39_binding j).symm
  · exact (CFSGSuzPackedRows40To47.raw_row_40_binding j).trans (CFSGSuzPackedRows40To47.packed_row_40_binding j).symm
  · exact (CFSGSuzPackedRows40To47.raw_row_41_binding j).trans (CFSGSuzPackedRows40To47.packed_row_41_binding j).symm
  · exact (CFSGSuzPackedRows40To47.raw_row_42_binding j).trans (CFSGSuzPackedRows40To47.packed_row_42_binding j).symm
  · exact (CFSGSuzPackedRows40To47.raw_row_43_binding j).trans (CFSGSuzPackedRows40To47.packed_row_43_binding j).symm
  · exact (CFSGSuzPackedRows40To47.raw_row_44_binding j).trans (CFSGSuzPackedRows40To47.packed_row_44_binding j).symm
  · exact (CFSGSuzPackedRows40To47.raw_row_45_binding j).trans (CFSGSuzPackedRows40To47.packed_row_45_binding j).symm
  · exact (CFSGSuzPackedRows40To47.raw_row_46_binding j).trans (CFSGSuzPackedRows40To47.packed_row_46_binding j).symm
  · exact (CFSGSuzPackedRows40To47.raw_row_47_binding j).trans (CFSGSuzPackedRows40To47.packed_row_47_binding j).symm
  · exact (CFSGSuzPackedRows48To55.raw_row_48_binding j).trans (CFSGSuzPackedRows48To55.packed_row_48_binding j).symm
  · exact (CFSGSuzPackedRows48To55.raw_row_49_binding j).trans (CFSGSuzPackedRows48To55.packed_row_49_binding j).symm
  · exact (CFSGSuzPackedRows48To55.raw_row_50_binding j).trans (CFSGSuzPackedRows48To55.packed_row_50_binding j).symm
  · exact (CFSGSuzPackedRows48To55.raw_row_51_binding j).trans (CFSGSuzPackedRows48To55.packed_row_51_binding j).symm
  · exact (CFSGSuzPackedRows48To55.raw_row_52_binding j).trans (CFSGSuzPackedRows48To55.packed_row_52_binding j).symm
  · exact (CFSGSuzPackedRows48To55.raw_row_53_binding j).trans (CFSGSuzPackedRows48To55.packed_row_53_binding j).symm
  · exact (CFSGSuzPackedRows48To55.raw_row_54_binding j).trans (CFSGSuzPackedRows48To55.packed_row_54_binding j).symm
  · exact (CFSGSuzPackedRows48To55.raw_row_55_binding j).trans (CFSGSuzPackedRows48To55.packed_row_55_binding j).symm
  · exact (CFSGSuzPackedRows56To63.raw_row_56_binding j).trans (CFSGSuzPackedRows56To63.packed_row_56_binding j).symm
  · exact (CFSGSuzPackedRows56To63.raw_row_57_binding j).trans (CFSGSuzPackedRows56To63.packed_row_57_binding j).symm
  · exact (CFSGSuzPackedRows56To63.raw_row_58_binding j).trans (CFSGSuzPackedRows56To63.packed_row_58_binding j).symm
  · exact (CFSGSuzPackedRows56To63.raw_row_59_binding j).trans (CFSGSuzPackedRows56To63.packed_row_59_binding j).symm
  · exact (CFSGSuzPackedRows56To63.raw_row_60_binding j).trans (CFSGSuzPackedRows56To63.packed_row_60_binding j).symm
  · exact (CFSGSuzPackedRows56To63.raw_row_61_binding j).trans (CFSGSuzPackedRows56To63.packed_row_61_binding j).symm
  · exact (CFSGSuzPackedRows56To63.raw_row_62_binding j).trans (CFSGSuzPackedRows56To63.packed_row_62_binding j).symm
  · exact (CFSGSuzPackedRows56To63.raw_row_63_binding j).trans (CFSGSuzPackedRows56To63.packed_row_63_binding j).symm

private theorem second_row_00 : ∀ j : Fin 64,
    rawDigit rows2 0 j.val=packedDigit 2 (secondRowCode 0) j.val := by
  decide +kernel

private theorem second_row_01 : ∀ j : Fin 64,
    rawDigit rows2 1 j.val=packedDigit 2 (secondRowCode 1) j.val := by
  decide +kernel

private theorem second_row_02 : ∀ j : Fin 64,
    rawDigit rows2 2 j.val=packedDigit 2 (secondRowCode 2) j.val := by
  decide +kernel

private theorem second_row_03 : ∀ j : Fin 64,
    rawDigit rows2 3 j.val=packedDigit 2 (secondRowCode 3) j.val := by
  decide +kernel

private theorem second_row_04 : ∀ j : Fin 64,
    rawDigit rows2 4 j.val=packedDigit 2 (secondRowCode 4) j.val := by
  decide +kernel

private theorem second_row_05 : ∀ j : Fin 64,
    rawDigit rows2 5 j.val=packedDigit 2 (secondRowCode 5) j.val := by
  decide +kernel

private theorem second_row_06 : ∀ j : Fin 64,
    rawDigit rows2 6 j.val=packedDigit 2 (secondRowCode 6) j.val := by
  decide +kernel

private theorem second_row_07 : ∀ j : Fin 64,
    rawDigit rows2 7 j.val=packedDigit 2 (secondRowCode 7) j.val := by
  decide +kernel

private theorem second_row_08 : ∀ j : Fin 64,
    rawDigit rows2 8 j.val=packedDigit 2 (secondRowCode 8) j.val := by
  decide +kernel

private theorem second_row_09 : ∀ j : Fin 64,
    rawDigit rows2 9 j.val=packedDigit 2 (secondRowCode 9) j.val := by
  decide +kernel

private theorem second_row_10 : ∀ j : Fin 64,
    rawDigit rows2 10 j.val=packedDigit 2 (secondRowCode 10) j.val := by
  decide +kernel

private theorem second_row_11 : ∀ j : Fin 64,
    rawDigit rows2 11 j.val=packedDigit 2 (secondRowCode 11) j.val := by
  decide +kernel

private theorem second_row_12 : ∀ j : Fin 64,
    rawDigit rows2 12 j.val=packedDigit 2 (secondRowCode 12) j.val := by
  decide +kernel

private theorem second_row_13 : ∀ j : Fin 64,
    rawDigit rows2 13 j.val=packedDigit 2 (secondRowCode 13) j.val := by
  decide +kernel

private theorem second_row_14 : ∀ j : Fin 64,
    rawDigit rows2 14 j.val=packedDigit 2 (secondRowCode 14) j.val := by
  decide +kernel

private theorem second_row_15 : ∀ j : Fin 64,
    rawDigit rows2 15 j.val=packedDigit 2 (secondRowCode 15) j.val := by
  decide +kernel

private theorem second_row_16 : ∀ j : Fin 64,
    rawDigit rows2 16 j.val=packedDigit 2 (secondRowCode 16) j.val := by
  decide +kernel

private theorem second_row_17 : ∀ j : Fin 64,
    rawDigit rows2 17 j.val=packedDigit 2 (secondRowCode 17) j.val := by
  decide +kernel

private theorem second_row_18 : ∀ j : Fin 64,
    rawDigit rows2 18 j.val=packedDigit 2 (secondRowCode 18) j.val := by
  decide +kernel

private theorem second_row_19 : ∀ j : Fin 64,
    rawDigit rows2 19 j.val=packedDigit 2 (secondRowCode 19) j.val := by
  decide +kernel

private theorem second_row_20 : ∀ j : Fin 64,
    rawDigit rows2 20 j.val=packedDigit 2 (secondRowCode 20) j.val := by
  decide +kernel

private theorem second_row_21 : ∀ j : Fin 64,
    rawDigit rows2 21 j.val=packedDigit 2 (secondRowCode 21) j.val := by
  decide +kernel

private theorem second_row_22 : ∀ j : Fin 64,
    rawDigit rows2 22 j.val=packedDigit 2 (secondRowCode 22) j.val := by
  decide +kernel

private theorem second_row_23 : ∀ j : Fin 64,
    rawDigit rows2 23 j.val=packedDigit 2 (secondRowCode 23) j.val := by
  decide +kernel

private theorem second_row_24 : ∀ j : Fin 64,
    rawDigit rows2 24 j.val=packedDigit 2 (secondRowCode 24) j.val := by
  decide +kernel

private theorem second_row_25 : ∀ j : Fin 64,
    rawDigit rows2 25 j.val=packedDigit 2 (secondRowCode 25) j.val := by
  decide +kernel

private theorem second_row_26 : ∀ j : Fin 64,
    rawDigit rows2 26 j.val=packedDigit 2 (secondRowCode 26) j.val := by
  decide +kernel

private theorem second_row_27 : ∀ j : Fin 64,
    rawDigit rows2 27 j.val=packedDigit 2 (secondRowCode 27) j.val := by
  decide +kernel

private theorem second_row_28 : ∀ j : Fin 64,
    rawDigit rows2 28 j.val=packedDigit 2 (secondRowCode 28) j.val := by
  decide +kernel

private theorem second_row_29 : ∀ j : Fin 64,
    rawDigit rows2 29 j.val=packedDigit 2 (secondRowCode 29) j.val := by
  decide +kernel

private theorem second_row_30 : ∀ j : Fin 64,
    rawDigit rows2 30 j.val=packedDigit 2 (secondRowCode 30) j.val := by
  decide +kernel

private theorem second_row_31 : ∀ j : Fin 64,
    rawDigit rows2 31 j.val=packedDigit 2 (secondRowCode 31) j.val := by
  decide +kernel

private theorem second_row_32 : ∀ j : Fin 64,
    rawDigit rows2 32 j.val=packedDigit 2 (secondRowCode 32) j.val := by
  decide +kernel

private theorem second_row_33 : ∀ j : Fin 64,
    rawDigit rows2 33 j.val=packedDigit 2 (secondRowCode 33) j.val := by
  decide +kernel

private theorem second_row_34 : ∀ j : Fin 64,
    rawDigit rows2 34 j.val=packedDigit 2 (secondRowCode 34) j.val := by
  decide +kernel

private theorem second_row_35 : ∀ j : Fin 64,
    rawDigit rows2 35 j.val=packedDigit 2 (secondRowCode 35) j.val := by
  decide +kernel

private theorem second_row_36 : ∀ j : Fin 64,
    rawDigit rows2 36 j.val=packedDigit 2 (secondRowCode 36) j.val := by
  decide +kernel

private theorem second_row_37 : ∀ j : Fin 64,
    rawDigit rows2 37 j.val=packedDigit 2 (secondRowCode 37) j.val := by
  decide +kernel

private theorem second_row_38 : ∀ j : Fin 64,
    rawDigit rows2 38 j.val=packedDigit 2 (secondRowCode 38) j.val := by
  decide +kernel

private theorem second_row_39 : ∀ j : Fin 64,
    rawDigit rows2 39 j.val=packedDigit 2 (secondRowCode 39) j.val := by
  decide +kernel

private theorem second_row_40 : ∀ j : Fin 64,
    rawDigit rows2 40 j.val=packedDigit 2 (secondRowCode 40) j.val := by
  decide +kernel

private theorem second_row_41 : ∀ j : Fin 64,
    rawDigit rows2 41 j.val=packedDigit 2 (secondRowCode 41) j.val := by
  decide +kernel

private theorem second_row_42 : ∀ j : Fin 64,
    rawDigit rows2 42 j.val=packedDigit 2 (secondRowCode 42) j.val := by
  decide +kernel

private theorem second_row_43 : ∀ j : Fin 64,
    rawDigit rows2 43 j.val=packedDigit 2 (secondRowCode 43) j.val := by
  decide +kernel

private theorem second_row_44 : ∀ j : Fin 64,
    rawDigit rows2 44 j.val=packedDigit 2 (secondRowCode 44) j.val := by
  decide +kernel

private theorem second_row_45 : ∀ j : Fin 64,
    rawDigit rows2 45 j.val=packedDigit 2 (secondRowCode 45) j.val := by
  decide +kernel

private theorem second_row_46 : ∀ j : Fin 64,
    rawDigit rows2 46 j.val=packedDigit 2 (secondRowCode 46) j.val := by
  decide +kernel

private theorem second_row_47 : ∀ j : Fin 64,
    rawDigit rows2 47 j.val=packedDigit 2 (secondRowCode 47) j.val := by
  decide +kernel

private theorem second_row_48 : ∀ j : Fin 64,
    rawDigit rows2 48 j.val=packedDigit 2 (secondRowCode 48) j.val := by
  decide +kernel

private theorem second_row_49 : ∀ j : Fin 64,
    rawDigit rows2 49 j.val=packedDigit 2 (secondRowCode 49) j.val := by
  decide +kernel

private theorem second_row_50 : ∀ j : Fin 64,
    rawDigit rows2 50 j.val=packedDigit 2 (secondRowCode 50) j.val := by
  decide +kernel

private theorem second_row_51 : ∀ j : Fin 64,
    rawDigit rows2 51 j.val=packedDigit 2 (secondRowCode 51) j.val := by
  decide +kernel

private theorem second_row_52 : ∀ j : Fin 64,
    rawDigit rows2 52 j.val=packedDigit 2 (secondRowCode 52) j.val := by
  decide +kernel

private theorem second_row_53 : ∀ j : Fin 64,
    rawDigit rows2 53 j.val=packedDigit 2 (secondRowCode 53) j.val := by
  decide +kernel

private theorem second_row_54 : ∀ j : Fin 64,
    rawDigit rows2 54 j.val=packedDigit 2 (secondRowCode 54) j.val := by
  decide +kernel

private theorem second_row_55 : ∀ j : Fin 64,
    rawDigit rows2 55 j.val=packedDigit 2 (secondRowCode 55) j.val := by
  decide +kernel

private theorem second_row_56 : ∀ j : Fin 64,
    rawDigit rows2 56 j.val=packedDigit 2 (secondRowCode 56) j.val := by
  decide +kernel

private theorem second_row_57 : ∀ j : Fin 64,
    rawDigit rows2 57 j.val=packedDigit 2 (secondRowCode 57) j.val := by
  decide +kernel

private theorem second_row_58 : ∀ j : Fin 64,
    rawDigit rows2 58 j.val=packedDigit 2 (secondRowCode 58) j.val := by
  decide +kernel

private theorem second_row_59 : ∀ j : Fin 64,
    rawDigit rows2 59 j.val=packedDigit 2 (secondRowCode 59) j.val := by
  decide +kernel

private theorem second_row_60 : ∀ j : Fin 64,
    rawDigit rows2 60 j.val=packedDigit 2 (secondRowCode 60) j.val := by
  decide +kernel

private theorem second_row_61 : ∀ j : Fin 64,
    rawDigit rows2 61 j.val=packedDigit 2 (secondRowCode 61) j.val := by
  decide +kernel

private theorem second_row_62 : ∀ j : Fin 64,
    rawDigit rows2 62 j.val=packedDigit 2 (secondRowCode 62) j.val := by
  decide +kernel

private theorem second_row_63 : ∀ j : Fin 64,
    rawDigit rows2 63 j.val=packedDigit 2 (secondRowCode 63) j.val := by
  decide +kernel

theorem second_row_binding (i j : Fin 64) :
    rawDigit rows2 i.val j.val=packedDigit 2 (secondRowCode i.val) j.val := by
  fin_cases i
  · exact second_row_00 j
  · exact second_row_01 j
  · exact second_row_02 j
  · exact second_row_03 j
  · exact second_row_04 j
  · exact second_row_05 j
  · exact second_row_06 j
  · exact second_row_07 j
  · exact second_row_08 j
  · exact second_row_09 j
  · exact second_row_10 j
  · exact second_row_11 j
  · exact second_row_12 j
  · exact second_row_13 j
  · exact second_row_14 j
  · exact second_row_15 j
  · exact second_row_16 j
  · exact second_row_17 j
  · exact second_row_18 j
  · exact second_row_19 j
  · exact second_row_20 j
  · exact second_row_21 j
  · exact second_row_22 j
  · exact second_row_23 j
  · exact second_row_24 j
  · exact second_row_25 j
  · exact second_row_26 j
  · exact second_row_27 j
  · exact second_row_28 j
  · exact second_row_29 j
  · exact second_row_30 j
  · exact second_row_31 j
  · exact second_row_32 j
  · exact second_row_33 j
  · exact second_row_34 j
  · exact second_row_35 j
  · exact second_row_36 j
  · exact second_row_37 j
  · exact second_row_38 j
  · exact second_row_39 j
  · exact second_row_40 j
  · exact second_row_41 j
  · exact second_row_42 j
  · exact second_row_43 j
  · exact second_row_44 j
  · exact second_row_45 j
  · exact second_row_46 j
  · exact second_row_47 j
  · exact second_row_48 j
  · exact second_row_49 j
  · exact second_row_50 j
  · exact second_row_51 j
  · exact second_row_52 j
  · exact second_row_53 j
  · exact second_row_54 j
  · exact second_row_55 j
  · exact second_row_56 j
  · exact second_row_57 j
  · exact second_row_58 j
  · exact second_row_59 j
  · exact second_row_60 j
  · exact second_row_61 j
  · exact second_row_62 j
  · exact second_row_63 j

end SymmetricSubgroupAsymptotics.CFSGSuzSelectedProductPrimeThirteenRows
