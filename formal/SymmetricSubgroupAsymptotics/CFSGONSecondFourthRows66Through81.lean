import SymmetricSubgroupAsymptotics.CFSGONSelectedSecondFourthRowPilot

/-! ONE selected bounded block of original ON B^4 rows,
66..81. All numerical commands are separate
per row. Checked source columns are reused. No full matrix identity. -/
set_option autoImplicit false
set_option Elab.async false
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows66Through81
open MatrixNaturalRowDotReflection MatrixNaturalRowPowerReflection
open CFSG.Models.MatrixGroups.ON
open CFSGONSelectedSecondFourthRowPilot (columnCode source_column_binding)

namespace Row66

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 5444517870735015415413993718908291383296
  | 1 => 1099511627776
  | 2 => 1152921504606846976
  | 3 => 1237940039285380274899124224
  | 4 => 5444517870735015415413993718908291383296
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 66 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 66 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 66 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 66 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 66 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 66 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row66

namespace Row67

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 21778071482940061661655974875633165533184
  | 1 => 20769187434441541969025642610556930
  | 2 => 1496577676626844609009760702840784326249660240887840
  | 3 => 1496577676648622659723513330967592696810622676893729
  | 4 => 21778071482940061661655974875633165533184
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 67 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 67 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 67 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 67 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 67 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 67 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row67

namespace Row68

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 87112285931760246646623899502532662132736
  | 1 => 401734511064747568885490523085290650630550748445698208825344
  | 2 => 4611686018427387904
  | 3 => 4951760157141521099596496896
  | 4 => 87112285931760246646623899502532662132736
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 68 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 68 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 68 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 68 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 68 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 68 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row68

namespace Row69

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 348449143727040986586495598010130648530944
  | 1 => 1606938044258990275541962092341162602522202993782792835301376
  | 2 => 124330809102446660538845562036705210025114037699336929360115994223289874253133343883264
  | 3 => 306908903117234804522845182737761393687925193707447291303264159720268140391961838938205999681
  | 4 => 348449143727040986586495598010130648530944
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 69 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 69 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 69 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 69 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 69 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 69 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row69

namespace Row70

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 1393796574908163946345982392040522594123776
  | 1 => 25711008708143844408671393477458601640355247900524685364822016
  | 2 => 18446744073709551616
  | 3 => 19807040628566084398385987584
  | 4 => 1393796574908163946345982392040522594123776
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 70 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 70 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 70 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 70 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 70 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 70 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row70

namespace Row71

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 5575186299632655785383929568162090376495104
  | 1 => 411376139330301510538742295639337626245683966408394965837152256
  | 2 => 127314748520905380391777855525586135065716774604121015664758778084648831235208544136462336
  | 3 => 79228162514264337593543950336
  | 4 => 5575186299632655785383929568162090376495104
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 71 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 71 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 71 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 71 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 71 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 71 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row71

namespace Row72

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 22300745198530623141535718272648361505980416
  | 1 => 1645504557321206042154969182557350504982735865633579863348609024
  | 2 => 2037035976334486086268445688409378161051468393665936250636140449354381299763336706183397376
  | 3 => 52219602553956693048657739409464055110224767032292044177702573307809020812132605521824933269
  | 4 => 22300745198530623141535718272648361505980416
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 72 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 72 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 72 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 72 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 72 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 72 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row72

namespace Row73

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 89202980794122492566142873090593446023921664
  | 1 => 26328072917139296674479506920917608079723773850137277813577744384
  | 2 => 130370302485407109521180524058200202307293977194619920040712988758680403184853549195737432064
  | 3 => 1267650600228229401496703205376
  | 4 => 89202980794122492566142873090593446023921664
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 73 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 73 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 73 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 73 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 73 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 73 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row73

namespace Row74

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 356811923176489970264571492362373784095686656
  | 1 => 105312291668557186697918027683670432318895095400549111254310977536
  | 2 => 171185127830983319819544812015279218498100092414026890062972921977646687909162480858771827082
  | 3 => 171176933385803896137396030368844549965320815501474677708605221875855804535207299420094204433
  | 4 => 356811923176489970264571492362373784095686656
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 74 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 74 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 74 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 74 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 74 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 74 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row74

namespace Row75

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 1427247692705959881058285969449495136382746624
  | 1 => 70368744177664
  | 2 => 295147905179352825856
  | 3 => 5070602400912917605986812821504
  | 4 => 1427247692705959881058285969449495136382746624
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 75 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 75 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 75 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 75 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 75 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 75 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row75

namespace Row76

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 5708990770823839524233143877797980545530986496
  | 1 => 1684996666696914987166688442938726917102321526408785780068975640576
  | 2 => 4726851485832529630037150653417516720494771175268457416925567087007957510038423695214019669
  | 3 => 814930827180348548466311882140564404553719332531745156455847919466408732829745093418265096
  | 4 => 5708990770823839524233143877797980545530986496
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 76 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 76 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 76 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 76 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 76 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 76 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row76

namespace Row77

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 22835963083295358096932575511191922182123945984
  | 1 => 26959946667150639794667015087019630673637144422540572481103610249216
  | 2 => 1180591620717411303424
  | 3 => 20282409603651670423947251286016
  | 4 => 22835963083295358096932575511191922182123945984
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 77 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 77 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 77 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 77 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 77 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 77 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row77

namespace Row78

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 91343852333181432387730302044767688728495783936
  | 1 => 431359146674410236714672241392314090778194310760649159697657763987456
  | 2 => 302034615187171979307516848529413206773907681608956289624774289218964008946371567499371119713
  | 3 => 81129638414606681695789005144064
  | 4 => 91343852333181432387730302044767688728495783936
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 78 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 78 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 78 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 78 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 78 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 78 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row78

namespace Row79

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 365375409332725729550921208179070754913983135744
  | 1 => 1725436586697640946858688965569256363112777243042596638790631055949824
  | 2 => 10257338663609171986350209296027393618883688092286399023543390632766238900307227897240262656
  | 3 => 343005890589446866862435080600148411403808371808479378892871664301343786353832681622924728586
  | 4 => 365375409332725729550921208179070754913983135744
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 79 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 79 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 79 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 79 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 79 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 79 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row79

namespace Row80

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 1461501637330902918203684832716283019655932542976
  | 1 => 1125899906842624
  | 2 => 4722366482869645213696
  | 3 => 324518553658426726783156020576256
  | 4 => 1461501637330902918203684832716283019655932542976
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 80 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 80 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 80 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 80 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 80 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 80 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row80

namespace Row81

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 5846006549323611672814739330865132078623730171904
  | 1 => 27606985387162255149739023449108101809804435888681546220650096895197184
  | 2 => 53676109065089758379483220309213674817820618405563925646882758839756744961425337178242853272
  | 3 => 204722942064865511537707941223589131385444353570412567328037864022408978237652518664557121574
  | 4 => 5846006549323611672814739330865132078623730171904
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 81 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 81 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 81 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 81 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 81 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 81 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row81

theorem block_identity (i : Fin 16) (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) ⟨i.val + 66, by omega⟩ z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) ⟨i.val + 66, by omega⟩ z := by
  fin_cases i
  · exact Row66.row_identity z
  · exact Row67.row_identity z
  · exact Row68.row_identity z
  · exact Row69.row_identity z
  · exact Row70.row_identity z
  · exact Row71.row_identity z
  · exact Row72.row_identity z
  · exact Row73.row_identity z
  · exact Row74.row_identity z
  · exact Row75.row_identity z
  · exact Row76.row_identity z
  · exact Row77.row_identity z
  · exact Row78.row_identity z
  · exact Row79.row_identity z
  · exact Row80.row_identity z
  · exact Row81.row_identity z

end SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows66Through81
