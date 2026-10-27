import SymmetricSubgroupAsymptotics.CFSGONSelectedSecondFourthRowPilot

/-! ONE selected bounded block of original ON B^4 rows,
98..113. All numerical commands are separate
per row. Checked source columns are reused. No full matrix identity. -/
set_option autoImplicit false
set_option Elab.async false
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows98Through113
open MatrixNaturalRowDotReflection MatrixNaturalRowPowerReflection
open CFSG.Models.MatrixGroups.ON
open CFSGONSelectedSecondFourthRowPilot (columnCode source_column_binding)

namespace Row98

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 100433627766186892221372630771322662657637687111424552206336
  | 1 => 31082702275611665134711390509176302506278509424834232340028998555822468563283335970816
  | 2 => 295450460647191811810889817619219943394467686453091662569530219677692255662475444878070940245
  | 3 => 53615967703916765418696244650999272271844686610188480874133811542973686632963018527717089321
  | 4 => 100433627766186892221372630771322662657637687111424552206336
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 98 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 98 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 98 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 98 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 98 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 98 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row98

namespace Row99

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 401734511064747568885490523085290650630550748445698208825344
  | 1 => 4611686018427387904
  | 2 => 4951760157141521099596496896
  | 3 => 87112285931760246646623899502532662132736
  | 4 => 401734511064747568885490523085290650630550748445698208825344
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 99 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 99 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 99 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 99 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 99 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 99 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row99

namespace Row100

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 1606938044258990275541962092341162602522202993782792835301376
  | 1 => 124330809102446660538845562036705210025114037699336929360115994223289874253133343883264
  | 2 => 306908903117234804522845182737761393687925193707447291303264159720268140391961838938205999681
  | 3 => 348449143727040986586495598010130648530944
  | 4 => 1606938044258990275541962092341162602522202993782792835301376
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 100 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 100 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 100 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 100 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 100 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 100 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row100

namespace Row101

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 6427752177035961102167848369364650410088811975131171341205504
  | 1 => 497323236409786642155382248146820840100456150797347717440463976893159497012533375533056
  | 2 => 184616880426823666441203123824063561306442847735156550712883307039219759027698092656747225177
  | 3 => 65872018993691918147906964995044250572921190636336808154355296351896074883577387596601762840
  | 4 => 6427752177035961102167848369364650410088811975131171341205504
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 101 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 101 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 101 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 101 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 101 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 101 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row101

namespace Row102

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 25711008708143844408671393477458601640355247900524685364822016
  | 1 => 18446744073709551616
  | 2 => 19807040628566084398385987584
  | 3 => 1393796574908163946345982392040522594123776
  | 4 => 25711008708143844408671393477458601640355247900524685364822016
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 102 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 102 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 102 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 102 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 102 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 102 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row102

namespace Row103

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 102844034832575377634685573909834406561420991602098741459288064
  | 1 => 7957171782556586274486115970349133441607298412757563479047423630290551952200534008528896
  | 2 => 179837229161890588290118324295903857615147369524460203800677455228109267421063331567500953625
  | 3 => 302520546117586184721644148237502985468061298593512955132495560108416420252310685172260688969
  | 4 => 102844034832575377634685573909834406561420991602098741459288064
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 103 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 103 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 103 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 103 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 103 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 103 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row103

namespace Row104

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 411376139330301510538742295639337626245683966408394965837152256
  | 1 => 127314748520905380391777855525586135065716774604121015664758778084648831235208544136462336
  | 2 => 79228162514264337593543950336
  | 3 => 5575186299632655785383929568162090376495104
  | 4 => 411376139330301510538742295639337626245683966408394965837152256
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 104 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 104 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 104 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 104 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 104 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 104 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row104

namespace Row105

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 1645504557321206042154969182557350504982735865633579863348609024
  | 1 => 2037035976334486086268445688409378161051468393665936250636140449354381299763336706183397376
  | 2 => 52219602553956693048657739409464055110224767032292044177702573307809020812132605521824933269
  | 3 => 22300745198530623141535718272648361505980416
  | 4 => 1645504557321206042154969182557350504982735865633579863348609024
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 105 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 105 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 105 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 105 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 105 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 105 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row105

namespace Row106

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 6582018229284824168619876730229402019930943462534319453394436096
  | 1 => 8148143905337944345073782753637512644205873574663745002544561797417525199053346824733589504
  | 2 => 131529267846921953664429623643644324718106198162543656096475598291196165510031112810503227926
  | 3 => 21055967027066828946819845875228461999163109057246102146288464547455647218121485878431326505
  | 4 => 6582018229284824168619876730229402019930943462534319453394436096
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 106 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 106 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 106 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 106 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 106 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 106 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row106

namespace Row107

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 26328072917139296674479506920917608079723773850137277813577744384
  | 1 => 130370302485407109521180524058200202307293977194619920040712988758680403184853549195737432064
  | 2 => 1267650600228229401496703205376
  | 3 => 89202980794122492566142873090593446023921664
  | 4 => 26328072917139296674479506920917608079723773850137277813577744384
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 107 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 107 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 107 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 107 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 107 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 107 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row107

namespace Row108

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 105312291668557186697918027683670432318895095400549111254310977536
  | 1 => 171185127830983319819544812015279218498100092414026890062972921977646687909162480858771827082
  | 2 => 171176933385803896137396030368844549965320815501474677708605221875855804535207299420094204433
  | 3 => 356811923176489970264571492362373784095686656
  | 4 => 105312291668557186697918027683670432318895095400549111254310977536
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 108 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 108 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 108 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 108 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 108 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 108 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row108

namespace Row109

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 421249166674228746791672110734681729275580381602196445017243910144
  | 1 => 217010262539762680779520894862375162752932810424133532372136265746253172065704473809767519784
  | 2 => 337458014837954028217273235260059020961145287160553347639075091412452802600303635759918113365
  | 3 => 67910989687681337134230009003060686059563892049004761139588462059833740196123760327911630368
  | 4 => 421249166674228746791672110734681729275580381602196445017243910144
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 109 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 109 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 109 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 109 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 109 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 109 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row109

namespace Row110

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 1684996666696914987166688442938726917102321526408785780068975640576
  | 1 => 4726851485832529630037150653417516720494771175268457416925567087007957510038423695214019669
  | 2 => 814930827180348548466311882140564404553719332531745156455847919466408732829745093418265096
  | 3 => 5708990770823839524233143877797980545530986496
  | 4 => 1684996666696914987166688442938726917102321526408785780068975640576
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 110 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 110 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 110 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 110 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 110 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 110 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row110

namespace Row111

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 6739986666787659948666753771754907668409286105635143120275902562304
  | 1 => 303711321952178852952265772649904732893218206059833540415645277645558277866214671380659676774
  | 2 => 84555934299653748644064056804923190828480873753819874824333886474551440245526862625255876128
  | 3 => 330196026331056600709837324218051785547706757438795660505350093409829686623980940374875120258
  | 4 => 6739986666787659948666753771754907668409286105635143120275902562304
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 111 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 111 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 111 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 111 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 111 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 111 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row111

namespace Row112

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 26959946667150639794667015087019630673637144422540572481103610249216
  | 1 => 1180591620717411303424
  | 2 => 20282409603651670423947251286016
  | 3 => 22835963083295358096932575511191922182123945984
  | 4 => 26959946667150639794667015087019630673637144422540572481103610249216
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 112 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 112 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 112 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 112 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 112 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 112 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row112

namespace Row113

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 107839786668602559178668060348078522694548577690162289924414440996864
  | 1 => 35935747834817741354074103793098675823927850962649094199561269155824999745644044507283865876
  | 2 => 304669306620530137645746014611849473051936989395805708479224742906521185969104837126243092560
  | 3 => 212058889071186118932714145819129638258673386650462879705517305854900863279612180581768118610
  | 4 => 107839786668602559178668060348078522694548577690162289924414440996864
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 113 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 113 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 113 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 113 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 113 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 113 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row113

theorem block_identity (i : Fin 16) (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) ⟨i.val + 98, by omega⟩ z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) ⟨i.val + 98, by omega⟩ z := by
  fin_cases i
  · exact Row98.row_identity z
  · exact Row99.row_identity z
  · exact Row100.row_identity z
  · exact Row101.row_identity z
  · exact Row102.row_identity z
  · exact Row103.row_identity z
  · exact Row104.row_identity z
  · exact Row105.row_identity z
  · exact Row106.row_identity z
  · exact Row107.row_identity z
  · exact Row108.row_identity z
  · exact Row109.row_identity z
  · exact Row110.row_identity z
  · exact Row111.row_identity z
  · exact Row112.row_identity z
  · exact Row113.row_identity z

end SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows98Through113
