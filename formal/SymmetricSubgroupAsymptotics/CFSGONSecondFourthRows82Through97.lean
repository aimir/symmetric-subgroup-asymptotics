import SymmetricSubgroupAsymptotics.CFSGONSelectedSecondFourthRowPilot

/-! ONE selected bounded block of original ON B^4 rows,
82..97. All numerical commands are separate
per row. Checked source columns are reused. No full matrix identity. -/
set_option autoImplicit false
set_option Elab.async false
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows82Through97
open MatrixNaturalRowDotReflection MatrixNaturalRowPowerReflection
open CFSG.Models.MatrixGroups.ON
open CFSGONSelectedSecondFourthRowPilot (columnCode source_column_binding)

namespace Row82

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 23384026197294446691258957323460528314494920687616
  | 1 => 441711766194596082395824375185729628956870974218904739530401550323154944
  | 2 => 18889465931478580854784
  | 3 => 1298074214633706907132624082305024
  | 4 => 23384026197294446691258957323460528314494920687616
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 82 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 82 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 82 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 82 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 82 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 82 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row82

namespace Row83

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 93536104789177786765035829293842113257979682750464
  | 1 => 7067388259113537318333190002971674063309935587502475832486424805170479104
  | 2 => 85588121660331236070071918478622714271494057774694440292915090264113803040943528091576451414
  | 3 => 5192296858534827628530496329220096
  | 4 => 93536104789177786765035829293842113257979682750464
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 83 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 83 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 83 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 83 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 83 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 83 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row83

namespace Row84

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 374144419156711147060143317175368453031918731001856
  | 1 => 28269553036454149273332760011886696253239742350009903329945699220681916416
  | 2 => 33365083085653543705283783883493442278794766162320093118626006705375819938784537453370352150
  | 3 => 131588252009249116901338795210469841561030829541332858791544400999314088519182890748576441940
  | 4 => 374144419156711147060143317175368453031918731001856
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 84 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 84 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 84 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 84 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 84 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 84 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row84

namespace Row85

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 1496577676626844588240573268701473812127674924007424
  | 1 => 21778071482940062266118884682947752886561
  | 2 => 302231454903657293676544
  | 3 => 20769187434139310514121985316880384
  | 4 => 1496577676626844588240573268701473812127674924007424
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 85 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 85 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 85 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 85 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 85 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 85 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row85

namespace Row86

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 5986310706507378352962293074805895248510699696029696
  | 1 => 1809251394333065553493296640760748560207343510400633813116524750123642650624
  | 2 => 175873688537930819832410824069424234419760838823246374820484813584354935674625679620173736086
  | 3 => 83076749736557242056487941267521536
  | 4 => 5986310706507378352962293074805895248510699696029696
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 86 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 86 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 86 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 86 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 86 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 86 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row86

namespace Row87

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 23945242826029513411849172299223580994042798784118784
  | 1 => 7237005577332262213973186563042994240829374041602535252466099000494570602496
  | 2 => 271721646289262542675847330098563656877659654459764073004120346616735260552281249470509748865
  | 3 => 278265580961883574263832754211357567537151998171934451253082223554979982874991301168240105801
  | 4 => 23945242826029513411849172299223580994042798784118784
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 87 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 87 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 87 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 87 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 87 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 87 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row87

namespace Row88

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 95780971304118053647396689196894323976171195136475136
  | 1 => 115792089237316195423570985008687907853269984665640564039457584007913129639936
  | 2 => 165318832824572755970516216376178964252878650717413631691079791170992942912224367858620736024
  | 3 => 1329227995784915872903807060280344576
  | 4 => 95780971304118053647396689196894323976171195136475136
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 88 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 88 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 88 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 88 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 88 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 88 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row88

namespace Row89

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 383123885216472214589586756787577295904684780545900544
  | 1 => 463168356949264781694283940034751631413079938662562256157830336031652518559744
  | 2 => 82647701035593609162238801105962443909765873698925975513485008173992659534511908018790619456
  | 3 => 135717563042151069754506104046991463725261140974055801317060398667051238207984806356957881636
  | 4 => 383123885216472214589586756787577295904684780545900544
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 89 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 89 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 89 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 89 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 89 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 89 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row89

namespace Row90

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 1532495540865888858358347027150309183618739122183602176
  | 1 => 72057594037927936
  | 2 => 4835703278458516698824704
  | 3 => 5316911983139663491615228241121378304
  | 4 => 1532495540865888858358347027150309183618739122183602176
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 90 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 90 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 90 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 90 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 90 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 90 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row90

namespace Row91

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 6129982163463555433433388108601236734474956488734408704
  | 1 => 7410693711188236507108543040556026102609279018600996098525285376506440296955904
  | 2 => 296685897152064660983505294070076340525949718547132480114863030307544951054296324187950819716
  | 3 => 334142240118190069465860133663886702102149915165890124490828675458772429906794648739374343434
  | 4 => 6129982163463555433433388108601236734474956488734408704
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 91 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 91 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 91 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 91 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 91 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 91 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row91

namespace Row92

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 24519928653854221733733552434404946937899825954937634816
  | 1 => 118571099379011784113736688648896417641748464297615937576404566024103044751294464
  | 2 => 19342813113834066795298816
  | 3 => 21267647932558653966460912964485513216
  | 4 => 24519928653854221733733552434404946937899825954937634816
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 92 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 92 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 92 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 92 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 92 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 92 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row92

namespace Row93

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 98079714615416886934934209737619787751599303819750539264
  | 1 => 1897137590064188545819787018382342682267975428761855001222473056385648716020711424
  | 2 => 37816712447323994196165055163884006033926359288295245638517253301357802893481991815510919770
  | 3 => 85070591730234615865843651857942052864
  | 4 => 98079714615416886934934209737619787751599303819750539264
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 93 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 93 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 93 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 93 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 93 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 93 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row93

namespace Row94

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 392318858461667547739736838950479151006397215279002157056
  | 1 => 7588550360256754183279148073529370729071901715047420004889892225542594864082845696
  | 2 => 310300485816955569781450174162957062554225420529401075582687610746041576230987830151516538026
  | 3 => 216725581909521329972359585883731682685652373200734266666734890801276922019655132591160628744
  | 4 => 392318858461667547739736838950479151006397215279002157056
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 94 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 94 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 94 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 94 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 94 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 94 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row94

namespace Row95

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 1569275433846670190958947355801916604025588861116008628224
  | 1 => 121416805764108066932466369176469931665150427440758720078238275608681517825325531136
  | 2 => 309485009821345068724781056
  | 3 => 340282366920938463463374607431768211456
  | 4 => 1569275433846670190958947355801916604025588861116008628224
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 95 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 95 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 95 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 95 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 95 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 95 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row95

namespace Row96

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 6277101735386680763835789423207666416102355444464034512896
  | 1 => 1942668892225729070919461906823518906642406839052139521251812409738904285205208498176
  | 2 => 78681169935539002302568107317423734959450588172137539501951643508459419777547614939504870922
  | 3 => 1361129467683753853853498429727072845824
  | 4 => 6277101735386680763835789423207666416102355444464034512896
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 96 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 96 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 96 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 96 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 96 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 96 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row96

namespace Row97

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 25108406941546723055343157692830665664409421777856138051584
  | 1 => 7770675568902916283677847627294075626569627356208558085007249638955617140820833992704
  | 2 => 18414964722301311043664671202286640149637932147505580169000408391405202764447655045477275305
  | 3 => 260777417744783814155561174764531032751347600152169049865553244434784603770603902134927398532
  | 4 => 25108406941546723055343157692830665664409421777856138051584
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 97 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 97 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 97 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 97 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 97 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 97 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row97

theorem block_identity (i : Fin 16) (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) ⟨i.val + 82, by omega⟩ z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) ⟨i.val + 82, by omega⟩ z := by
  fin_cases i
  · exact Row82.row_identity z
  · exact Row83.row_identity z
  · exact Row84.row_identity z
  · exact Row85.row_identity z
  · exact Row86.row_identity z
  · exact Row87.row_identity z
  · exact Row88.row_identity z
  · exact Row89.row_identity z
  · exact Row90.row_identity z
  · exact Row91.row_identity z
  · exact Row92.row_identity z
  · exact Row93.row_identity z
  · exact Row94.row_identity z
  · exact Row95.row_identity z
  · exact Row96.row_identity z
  · exact Row97.row_identity z

end SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows82Through97
