import SymmetricSubgroupAsymptotics.CFSGONSelectedSecondFourthRowPilot

/-! ONE selected bounded block of original ON B^4 rows,
114..129. All numerical commands are separate
per row. Checked source columns are reused. No full matrix identity. -/
set_option autoImplicit false
set_option Elab.async false
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows114Through129
open MatrixNaturalRowDotReflection MatrixNaturalRowPowerReflection
open CFSG.Models.MatrixGroups.ON
open CFSGONSelectedSecondFourthRowPilot (columnCode source_column_binding)

namespace Row114

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 431359146674410236714672241392314090778194310760649159697657763987456
  | 1 => 302034615187171979307516848529413206773907681608956289624774289218964008946371567499371119713
  | 2 => 81129638414606681695789005144064
  | 3 => 91343852333181432387730302044767688728495783936
  | 4 => 431359146674410236714672241392314090778194310760649159697657763987456
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 114 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 114 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 114 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 114 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 114 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 114 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row114

namespace Row115

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 1725436586697640946858688965569256363112777243042596638790631055949824
  | 1 => 10257338663609171986350209296027393618883688092286399023543390632766238900307227897240262656
  | 2 => 343005890589446866862435080600148411403808371808479378892871664301343786353832681622924728586
  | 3 => 365375409332725729550921208179070754913983135744
  | 4 => 1725436586697640946858688965569256363112777243042596638790631055949824
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 115 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 115 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 115 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 115 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 115 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 115 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row115

namespace Row116

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 6901746346790563787434755862277025452451108972170386555162524223799296
  | 1 => 133712830576339053761934984755487454584613029431641316963649785658885564448658313824650701409
  | 2 => 199791350288371592753943563224187405772316066034825479904344597786699621970625963268417802341
  | 3 => 329153435685005988931167332775181539532374201130372268422540631293693763332796070640171487366
  | 4 => 6901746346790563787434755862277025452451108972170386555162524223799296
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 116 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 116 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 116 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 116 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 116 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 116 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row116

namespace Row117

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 27606985387162255149739023449108101809804435888681546220650096895197184
  | 1 => 53676109065089758379483220309213674817820618405563925646882758839756744961425337178242853272
  | 2 => 204722942064865511537707941223589131385444353570412567328037864022408978237652518664557121574
  | 3 => 5846006549323611672814739330865132078623730171904
  | 4 => 27606985387162255149739023449108101809804435888681546220650096895197184
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 117 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 117 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 117 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 117 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 117 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 117 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row117

namespace Row118

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 110427941548649020598956093796432407239217743554726184882600387580788736
  | 1 => 53768848721993948794735368553904508723782297834471565292815952742637333633407711481828041990
  | 2 => 81691622977501969649600181704643108081106942753696925200233648765270328707075166242076797513
  | 3 => 206792973787124470278349045380873863668519515054039550589314537202824131780025119528747800934
  | 4 => 110427941548649020598956093796432407239217743554726184882600387580788736
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 118 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 118 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 118 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 118 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 118 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 118 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row118

namespace Row119

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 441711766194596082395824375185729628956870974218904739530401550323154944
  | 1 => 18889465931478580854784
  | 2 => 1298074214633706907132624082305024
  | 3 => 23384026197294446691258957323460528314494920687616
  | 4 => 441711766194596082395824375185729628956870974218904739530401550323154944
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 119 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 119 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 119 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 119 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 119 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 119 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row119

namespace Row120

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 1766847064778384329583297500742918515827483896875618958121606201292619776
  | 1 => 180281858974730822272763224714096153032108234680847784303162972418641758667308450592551231764
  | 2 => 326594300503777996701622806794438303679304100152041230803788224437038205446951360035153121857
  | 3 => 19639077212183159350192673611990900183866647441860428254216833720810230863977633524063147040
  | 4 => 1766847064778384329583297500742918515827483896875618958121606201292619776
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 120 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 120 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 120 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 120 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 120 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 120 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row120

namespace Row121

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 7067388259113537318333190002971674063309935587502475832486424805170479104
  | 1 => 85588121660331236070071918478622714271494057774694440292915090264113803040943528091576451414
  | 2 => 5192296858534827628530496329220096
  | 3 => 93536104789177786765035829293842113257979682750464
  | 4 => 7067388259113537318333190002971674063309935587502475832486424805170479104
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 121 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 121 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 121 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 121 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 121 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 121 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row121

namespace Row122

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 28269553036454149273332760011886696253239742350009903329945699220681916416
  | 1 => 33365083085653543705283783883493442278794766162320093118626006705375819938784537453370352150
  | 2 => 131588252009249116901338795210469841561030829541332858791544400999314088519182890748576441940
  | 3 => 374144419156711147060143317175368453031918731001856
  | 4 => 28269553036454149273332760011886696253239742350009903329945699220681916416
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 122 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 122 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 122 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 122 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 122 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 122 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row122

namespace Row123

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 113078212145816597093331040047546785012958969400039613319782796882727665664
  | 1 => 173784787452120886155090449216128976024202505915821148830294063517747302735936089803043465753
  | 2 => 151016004560443399748173852524213471959347182761604848568046432549572644666757206201950576725
  | 3 => 277104849473771119881213855972722593419482686719616486891247699255749979735124292003785113897
  | 4 => 113078212145816597093331040047546785012958969400039613319782796882727665664
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 123 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 123 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 123 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 123 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 123 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 123 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row123

namespace Row124

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 452312848583266388373324160190187140051835877600158453279131187530910662656
  | 1 => 331336962433363436329744856879219414879832492415297145409217102960066189293077190402442854809
  | 2 => 139300257249295075582755003912782278305287473076972484928223189473717937353240377380003400198
  | 3 => 303656805061430346391402338815406043946894387059100051272296036105830337730338539692323276440
  | 4 => 452312848583266388373324160190187140051835877600158453279131187530910662656
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 124 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 124 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 124 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 124 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 124 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 124 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row124

namespace Row125

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 1809251394333065553493296640760748560207343510400633813116524750123642650624
  | 1 => 175873688537930819832410824069424234419760838823246374820484813584354935674625679620173736086
  | 2 => 83076749736557242056487941267521536
  | 3 => 5986310706507378352962293074805895248510699696029696
  | 4 => 1809251394333065553493296640760748560207343510400633813116524750123642650624
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 125 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 125 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 125 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 125 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 125 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 125 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row125

namespace Row126

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 7237005577332262213973186563042994240829374041602535252466099000494570602496
  | 1 => 271721646289262542675847330098563656877659654459764073004120346616735260552281249470509748865
  | 2 => 278265580961883574263832754211357567537151998171934451253082223554979982874991301168240105801
  | 3 => 23945242826029513411849172299223580994042798784118784
  | 4 => 7237005577332262213973186563042994240829374041602535252466099000494570602496
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 126 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 126 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 126 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 126 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 126 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 126 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row126

namespace Row127

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 28948022309329048855892746252171976963317496166410141009864396001978282409984
  | 1 => 19354581955458070869380174730569418990345325355113180449365342128702857512573153941922538778
  | 2 => 84858563252525931304564729335510538621313595598859436384642431215256299716416984082124530214
  | 3 => 86903073669744749291678065235751465451648823298581198507731708519705447440019492433860581728
  | 4 => 28948022309329048855892746252171976963317496166410141009864396001978282409984
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 127 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 127 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 127 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 127 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 127 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 127 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row127

namespace Row128

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 115792089237316195423570985008687907853269984665640564039457584007913129639936
  | 1 => 165318832824572755970516216376178964252878650717413631691079791170992942912224367858620736024
  | 2 => 1329227995784915872903807060280344576
  | 3 => 95780971304118053647396689196894323976171195136475136
  | 4 => 115792089237316195423570985008687907853269984665640564039457584007913129639936
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 128 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 128 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 128 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 128 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 128 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 128 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row128

namespace Row129

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 463168356949264781694283940034751631413079938662562256157830336031652518559744
  | 1 => 82647701035593609162238801105962443909765873698925975513485008173992659534511908018790619456
  | 2 => 135717563042151069754506104046991463725261140974055801317060398667051238207984806356957881636
  | 3 => 383123885216472214589586756787577295904684780545900544
  | 4 => 463168356949264781694283940034751631413079938662562256157830336031652518559744
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 129 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 129 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 129 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 129 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 129 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 129 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row129

theorem block_identity (i : Fin 16) (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) ⟨i.val + 114, by omega⟩ z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) ⟨i.val + 114, by omega⟩ z := by
  fin_cases i
  · exact Row114.row_identity z
  · exact Row115.row_identity z
  · exact Row116.row_identity z
  · exact Row117.row_identity z
  · exact Row118.row_identity z
  · exact Row119.row_identity z
  · exact Row120.row_identity z
  · exact Row121.row_identity z
  · exact Row122.row_identity z
  · exact Row123.row_identity z
  · exact Row124.row_identity z
  · exact Row125.row_identity z
  · exact Row126.row_identity z
  · exact Row127.row_identity z
  · exact Row128.row_identity z
  · exact Row129.row_identity z

end SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows114Through129
