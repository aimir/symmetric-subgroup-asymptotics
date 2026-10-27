import SymmetricSubgroupAsymptotics.MatrixNaturalRowPowerReflection
import SymmetricSubgroupAsymptotics.External.CFSG.Models.MatrixGroups.Suz

/-! Exactly actual Suz rows1 A-square row0. Eight shared source-column
blocks bind all64columns. No other row, whole power or group-order claim. -/
set_option autoImplicit false
set_option Elab.async false
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGSuzFirstSquareRowZeroPilot
open MatrixNaturalRowDotReflection MatrixNaturalRowPowerReflection
open CFSG.Models.MatrixGroups.Suz

def columnCode (z : ℕ) : ℕ :=
  match z with
  | 0 => 85577187065045653950764877966807221606
  | 1 => 29607982973831176088868255019472933184
  | 2 => 192911130568455754728217049970761172512
  | 3 => 114751555611614528026616722986134233090
  | 4 => 109496617161444568025679662614372243601
  | 5 => 55937067282524008902395979766539392644
  | 6 => 224018575835353174831897138314614932872
  | 7 => 109103677859576003094870737056652367122
  | 8 => 90478862361281637683750053364836673090
  | 9 => 12088505479110223476070756063673190544
  | 10 => 45614982506691050288721170478383830602
  | 11 => 98394784024857388048941554334608544002
  | 12 => 49188272628033436064353050307974441001
  | 13 => 225410934093885142794948416719817377129
  | 14 => 178580807598983599687706878742019614786
  | 15 => 213472688808386052537475876842969244197
  | 16 => 139123174434737986919694864296699123362
  | 17 => 139657579126453063014853070507036125697
  | 18 => 119766829264696318015592306288848382249
  | 19 => 170942225388542439027011373400815347816
  | 20 => 43992414622324782709638946653014990914
  | 21 => 170556897162468072624131474114154760857
  | 22 => 85486838224903590668901463129858790980
  | 23 => 45737078996300575968024668886836584452
  | 24 => 90479132554406507840486170140474910212
  | 25 => 194786428265501725907744913853077014673
  | 26 => 129480512861792870536347465045684540490
  | 27 => 34087551366006822488854840835445989461
  | 28 => 56215266053301703259028569601816024362
  | 29 => 42756059775535156095385775885767032849
  | 30 => 194534721206900190122196488708326590985
  | 31 => 198078844205695088920894134982770533728
  | 32 => 21937565812291443168172383236445734150
  | 33 => 8102686491283467704282260484439214628
  | 34 => 192267520184918655538113430436591962502
  | 35 => 203834353217900705165951782390619081040
  | 36 => 138702234353865518969530677818385843609
  | 37 => 198767078584653632186262560926058422677
  | 38 => 98785418090391700792208364093471068840
  | 39 => 27943129747855810547181119541318090833
  | 40 => 219454182502001357949430531211215902794
  | 41 => 97160010123434092124174742825435407761
  | 42 => 91095370056911774150634330150304590214
  | 43 => 219351304106578851362753042202449041064
  | 44 => 135093390502111118615832978350185945674
  | 45 => 86753029531112651616657263790131680934
  | 46 => 224668597270963737578221389570057441920
  | 47 => 109828890863363176654968441574248720646
  | 48 => 692574093873135404331598395885525337
  | 49 => 91828802929140116255196475761791342752
  | 50 => 170307703965335070426669094099558487144
  | 51 => 213375297726226054080159406081446316066
  | 52 => 85763846155712071573668914296615766618
  | 53 => 112041501231267173629443482095718536218
  | 54 => 199908743866921067027198501348362709025
  | 55 => 11075380147197264084454070921985075862
  | 56 => 26777366568848896115371521578092349590
  | 57 => 88580590871563649189762089424697836041
  | 58 => 138433662442779735272059465829439607910
  | 59 => 218209633593527749277414665399083371174
  | 60 => 3081081986709397533926157467073483144
  | 61 => 86574300548563142889817948946932205698
  | 62 => 173570128348941498906567386890464550934
  | 63 => 22608125089794907577205585201288532502
  | _ => 0

theorem source_column_block_00 : ∀ (z : Fin 8) (j : Fin 64),
    rawDigit rows1 j.val (0 + z.val) =
      packedDigit 2 (columnCode (0 + z.val)) j.val := by
  decide +kernel

theorem source_column_block_01 : ∀ (z : Fin 8) (j : Fin 64),
    rawDigit rows1 j.val (8 + z.val) =
      packedDigit 2 (columnCode (8 + z.val)) j.val := by
  decide +kernel

theorem source_column_block_02 : ∀ (z : Fin 8) (j : Fin 64),
    rawDigit rows1 j.val (16 + z.val) =
      packedDigit 2 (columnCode (16 + z.val)) j.val := by
  decide +kernel

theorem source_column_block_03 : ∀ (z : Fin 8) (j : Fin 64),
    rawDigit rows1 j.val (24 + z.val) =
      packedDigit 2 (columnCode (24 + z.val)) j.val := by
  decide +kernel

theorem source_column_block_04 : ∀ (z : Fin 8) (j : Fin 64),
    rawDigit rows1 j.val (32 + z.val) =
      packedDigit 2 (columnCode (32 + z.val)) j.val := by
  decide +kernel

theorem source_column_block_05 : ∀ (z : Fin 8) (j : Fin 64),
    rawDigit rows1 j.val (40 + z.val) =
      packedDigit 2 (columnCode (40 + z.val)) j.val := by
  decide +kernel

theorem source_column_block_06 : ∀ (z : Fin 8) (j : Fin 64),
    rawDigit rows1 j.val (48 + z.val) =
      packedDigit 2 (columnCode (48 + z.val)) j.val := by
  decide +kernel

theorem source_column_block_07 : ∀ (z : Fin 8) (j : Fin 64),
    rawDigit rows1 j.val (56 + z.val) =
      packedDigit 2 (columnCode (56 + z.val)) j.val := by
  decide +kernel

theorem source_column_binding : ∀ (z j : Fin 64),
    rawDigit rows1 j.val z.val = packedDigit 2 (columnCode z.val) j.val := by
  intro z j
  by_cases hz00 : z.val < 8
  · let t : Fin 8 := ⟨z.val - 0, by omega⟩
    have he : 0 + t.val = z.val := by
      dsimp [t]
      omega
    have ht := source_column_block_00 t j
    rw [he] at ht
    exact ht
  by_cases hz01 : z.val < 16
  · let t : Fin 8 := ⟨z.val - 8, by omega⟩
    have he : 8 + t.val = z.val := by
      dsimp [t]
      omega
    have ht := source_column_block_01 t j
    rw [he] at ht
    exact ht
  by_cases hz02 : z.val < 24
  · let t : Fin 8 := ⟨z.val - 16, by omega⟩
    have he : 16 + t.val = z.val := by
      dsimp [t]
      omega
    have ht := source_column_block_02 t j
    rw [he] at ht
    exact ht
  by_cases hz03 : z.val < 32
  · let t : Fin 8 := ⟨z.val - 24, by omega⟩
    have he : 24 + t.val = z.val := by
      dsimp [t]
      omega
    have ht := source_column_block_03 t j
    rw [he] at ht
    exact ht
  by_cases hz04 : z.val < 40
  · let t : Fin 8 := ⟨z.val - 32, by omega⟩
    have he : 32 + t.val = z.val := by
      dsimp [t]
      omega
    have ht := source_column_block_04 t j
    rw [he] at ht
    exact ht
  by_cases hz05 : z.val < 48
  · let t : Fin 8 := ⟨z.val - 40, by omega⟩
    have he : 40 + t.val = z.val := by
      dsimp [t]
      omega
    have ht := source_column_block_05 t j
    rw [he] at ht
    exact ht
  by_cases hz06 : z.val < 56
  · let t : Fin 8 := ⟨z.val - 48, by omega⟩
    have he : 48 + t.val = z.val := by
      dsimp [t]
      omega
    have ht := source_column_block_06 t j
    rw [he] at ht
    exact ht
  let t : Fin 8 := ⟨z.val - 56, by omega⟩
  have he : 56 + t.val = z.val := by
    dsimp [t]
    omega
  have ht := source_column_block_07 t j
  rw [he] at ht
  exact ht

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 1
  | 1 => 224175358324649771740101499125688861058
  | 2 => 1
  | _ => 0

def rowVector (k : ℕ) (z : Fin 64) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 2) (z : Fin 64),
    packedDot 2 (stageCode k.val) (columnCode z.val) 64 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 64,
    rowVector 0 z = (1 : Matrix (Fin 64) (Fin 64) (ZMod 3)) 0 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 2) (z : Fin 64) :
    rowVector (k+1) z = ∑ j : Fin 64,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 64 rows1 j z := by
  exact (packed_row_step 3 64 2 rows1 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem square_power_row (z : Fin 64) :
    (CFSG.Models.MatrixData.matrix 3 64 rows1 ^ 2) 0 z = rowVector 2 z :=
  matrix_pow_row_eq 3 64 rows1 0 2 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 64,
    rowVector 2 z = (1 : Matrix (Fin 64) (Fin 64) (ZMod 3)) 0 z := by
  decide +kernel

theorem row_identity (z : Fin 64) :
    (CFSG.Models.MatrixData.matrix 3 64 rows1 ^ 2) 0 z =
      (1 : Matrix (Fin 64) (Fin 64) (ZMod 3)) 0 z :=
  (square_power_row z).trans (selected_row_return z)

end SymmetricSubgroupAsymptotics.CFSGSuzFirstSquareRowZeroPilot
