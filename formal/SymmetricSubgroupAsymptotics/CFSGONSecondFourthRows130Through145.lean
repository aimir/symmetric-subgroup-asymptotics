import SymmetricSubgroupAsymptotics.CFSGONSelectedSecondFourthRowPilot

/-! ONE selected bounded block of original ON B^4 rows,
130..145. All numerical commands are separate
per row. Checked source columns are reused. No full matrix identity. -/
set_option autoImplicit false
set_option Elab.async false
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows130Through145
open MatrixNaturalRowDotReflection MatrixNaturalRowPowerReflection
open CFSG.Models.MatrixGroups.ON
open CFSGONSelectedSecondFourthRowPilot (columnCode source_column_binding)

namespace Row130

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 1852673427797059126777135760139006525652319754650249024631321344126610074238976
  | 1 => 302518928031509547053666949608000677286204540550256750526984833126075963488616975154928854122
  | 2 => 198313735417391062483722471037811506875766850560646818396960619871763921767905517181697628546
  | 3 => 295374899388272658477993391686194753566940124525786428496619662750704288544783375770812319320
  | 4 => 1852673427797059126777135760139006525652319754650249024631321344126610074238976
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 130 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 130 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 130 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 130 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 130 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 130 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row130

namespace Row131

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 7410693711188236507108543040556026102609279018600996098525285376506440296955904
  | 1 => 296685897152064660983505294070076340525949718547132480114863030307544951054296324187950819716
  | 2 => 334142240118190069465860133663886702102149915165890124490828675458772429906794648739374343434
  | 3 => 6129982163463555433433388108601236734474956488734408704
  | 4 => 7410693711188236507108543040556026102609279018600996098525285376506440296955904
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 131 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 131 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 131 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 131 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 131 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 131 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row131

namespace Row132

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 29642774844752946028434172162224104410437116074403984394101141506025761187823616
  | 1 => 150774488162024144969219464479584467671132438377566121842588100143711595883928566141922844930
  | 2 => 133211180617431918362801567238652766434016769473763043689365383233686221997109247818730738024
  | 3 => 302547916386000013464888061560594506647557683955114685021090687710709698958646889474674694168
  | 4 => 29642774844752946028434172162224104410437116074403984394101141506025761187823616
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 132 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 132 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 132 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 132 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 132 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 132 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row132

namespace Row133

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 118571099379011784113736688648896417641748464297615937576404566024103044751294464
  | 1 => 19342813113834066795298816
  | 2 => 21267647932558653966460912964485513216
  | 3 => 24519928653854221733733552434404946937899825954937634816
  | 4 => 118571099379011784113736688648896417641748464297615937576404566024103044751294464
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 133 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 133 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 133 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 133 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 133 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 133 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row133

namespace Row134

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 474284397516047136454946754595585670566993857190463750305618264096412179005177856
  | 1 => 330581513988659278581159103331367355324570114102139909407786180611182015462572616987709183578
  | 2 => 298239448006726669929745897960616555422016241164504644302440026966092334504578203859554559105
  | 3 => 198786097594230002165089497246212237638798921602215196811074372386064820597874253198760969256
  | 4 => 474284397516047136454946754595585670566993857190463750305618264096412179005177856
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 134 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 134 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 134 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 134 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 134 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 134 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row134

namespace Row135

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 1897137590064188545819787018382342682267975428761855001222473056385648716020711424
  | 1 => 37816712447323994196165055163884006033926359288295245638517253301357802893481991815510919770
  | 2 => 85070591730234615865843651857942052864
  | 3 => 98079714615416886934934209737619787751599303819750539264
  | 4 => 1897137590064188545819787018382342682267975428761855001222473056385648716020711424
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 135 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 135 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 135 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 135 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 135 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 135 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row135

namespace Row136

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 7588550360256754183279148073529370729071901715047420004889892225542594864082845696
  | 1 => 310300485816955569781450174162957062554225420529401075582687610746041576230987830151516538026
  | 2 => 216725581909521329972359585883731682685652373200734266666734890801276922019655132591160628744
  | 3 => 392318858461667547739736838950479151006397215279002157056
  | 4 => 7588550360256754183279148073529370729071901715047420004889892225542594864082845696
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 136 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 136 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 136 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 136 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 136 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 136 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row136

namespace Row137

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 30354201441027016733116592294117482916287606860189680019559568902170379456331382784
  | 1 => 41504750963399465211178726122571770371658205569233421400716678579531566337188460179627852117
  | 2 => 204931550902430245709335163082429099144421519349374457722579751979652220882449056553777914912
  | 3 => 49225870393167775606447776559695334557816051759778141993093887636683869675818278092002060870
  | 4 => 30354201441027016733116592294117482916287606860189680019559568902170379456331382784
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 137 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 137 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 137 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 137 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 137 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 137 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row137

namespace Row138

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 121416805764108066932466369176469931665150427440758720078238275608681517825325531136
  | 1 => 309485009821345068724781056
  | 2 => 340282366920938463463374607431768211456
  | 3 => 1569275433846670190958947355801916604025588861116008628224
  | 4 => 121416805764108066932466369176469931665150427440758720078238275608681517825325531136
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 138 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 138 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 138 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 138 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 138 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 138 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row138

namespace Row139

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 485667223056432267729865476705879726660601709763034880312953102434726071301302124544
  | 1 => 143818749595628536527509436285055288399846593988461358325299947498848117732855159210244183365
  | 2 => 279275628814772039526057772073288179268672596045307032820546020912678272016622650130911794793
  | 3 => 329056970639910216867604312737340231607832730430722919795259291802949249482081698208585255528
  | 4 => 485667223056432267729865476705879726660601709763034880312953102434726071301302124544
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 139 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 139 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 139 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 139 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 139 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 139 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row139

namespace Row140

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 1942668892225729070919461906823518906642406839052139521251812409738904285205208498176
  | 1 => 78681169935539002302568107317423734959450588172137539501951643508459419777547614939504870922
  | 2 => 1361129467683753853853498429727072845824
  | 3 => 6277101735386680763835789423207666416102355444464034512896
  | 4 => 1942668892225729070919461906823518906642406839052139521251812409738904285205208498176
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 140 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 140 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 140 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 140 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 140 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 140 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row140

namespace Row141

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 7770675568902916283677847627294075626569627356208558085007249638955617140820833992704
  | 1 => 18414964722301311043664671202286640149637932147505580169000408391405202764447655045477275305
  | 2 => 260777417744783814155561174764531032751347600152169049865553244434784603770603902134927398532
  | 3 => 25108406941546723055343157692830665664409421777856138051584
  | 4 => 7770675568902916283677847627294075626569627356208558085007249638955617140820833992704
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 141 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 141 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 141 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 141 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 141 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 141 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row141

namespace Row142

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 31082702275611665134711390509176302506278509424834232340028998555822468563283335970816
  | 1 => 295450460647191811810889817619219943394467686453091662569530219677692255662475444878070940245
  | 2 => 53615967703916765418696244650999272271844686610188480874133811542973686632963018527717089321
  | 3 => 100433627766186892221372630771322662657637687111424552206336
  | 4 => 31082702275611665134711390509176302506278509424834232340028998555822468563283335970816
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 142 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 142 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 142 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 142 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 142 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 142 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row142

namespace Row143

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 124330809102446660538845562036705210025114037699336929360115994223289874253133343883264
  | 1 => 306908903117234804522845182737761393687925193707447291303264159720268140391961838938205999681
  | 2 => 348449143727040986586495598010130648530944
  | 3 => 1606938044258990275541962092341162602522202993782792835301376
  | 4 => 124330809102446660538845562036705210025114037699336929360115994223289874253133343883264
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 143 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 143 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 143 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 143 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 143 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 143 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row143

namespace Row144

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 497323236409786642155382248146820840100456150797347717440463976893159497012533375533056
  | 1 => 184616880426823666441203123824063561306442847735156550712883307039219759027698092656747225177
  | 2 => 65872018993691918147906964995044250572921190636336808154355296351896074883577387596601762840
  | 3 => 6427752177035961102167848369364650410088811975131171341205504
  | 4 => 497323236409786642155382248146820840100456150797347717440463976893159497012533375533056
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 144 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 144 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 144 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 144 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 144 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 144 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row144

namespace Row145

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 1989292945639146568621528992587283360401824603189390869761855907572637988050133502132224
  | 1 => 36877576048528562025202646786636960423182179906911641490295086807813924927204051676648024452
  | 2 => 171623028471711913327879652748032105201321101788251134261313248687711218054676169752589918378
  | 3 => 346348032548336289083312270131422618790877905170485902444857295417548086541961730014253764904
  | 4 => 1989292945639146568621528992587283360401824603189390869761855907572637988050133502132224
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 145 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 145 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 145 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 145 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 145 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 145 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row145

theorem block_identity (i : Fin 16) (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) ⟨i.val + 130, by omega⟩ z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) ⟨i.val + 130, by omega⟩ z := by
  fin_cases i
  · exact Row130.row_identity z
  · exact Row131.row_identity z
  · exact Row132.row_identity z
  · exact Row133.row_identity z
  · exact Row134.row_identity z
  · exact Row135.row_identity z
  · exact Row136.row_identity z
  · exact Row137.row_identity z
  · exact Row138.row_identity z
  · exact Row139.row_identity z
  · exact Row140.row_identity z
  · exact Row141.row_identity z
  · exact Row142.row_identity z
  · exact Row143.row_identity z
  · exact Row144.row_identity z
  · exact Row145.row_identity z

end SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows130Through145
