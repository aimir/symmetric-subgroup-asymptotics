import SymmetricSubgroupAsymptotics.CFSGSuzSelectedProductPrimeThirteenRows

/-! ONE selected positive AB vector orbit:26 original matrix applications,
13 word applications,64 coordinates. Eight fixed8-coordinate cohorts
per step keep every closed arithmetic command small. No resource
options or whole-matrix/group-order assertions are introduced. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGSuzSelectedProductPrimeThirteen
open MatrixNaturalRowDotReflection MatrixModelSelectedProductPrimePeriod
open CFSG.Models.MatrixGroups.Suz
open CFSGSuzSelectedProductPrimeThirteenRows
abbrev V := Fin 64 → ZMod 3
abbrev Model := CFSG.Models.MatrixGroups.Suz.Model

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 1
  | 1 => 109168741193826076872483311502021885985
  | 2 => 134359294271648286000125765529482454441
  | 3 => 50866997140970585706474804967126476377
  | 4 => 42589015139870285363853771140151911508
  | 5 => 193244716675886588969144349745753657876
  | 6 => 55029382038954042078918138924895307928
  | 7 => 182940404590272724488721899003532697604
  | 8 => 8163938637739385311766018595802597761
  | 9 => 135758158772086044599929552444456510561
  | 10 => 214137158353685273658946615888948122264
  | 11 => 99121378843233082505621185225975440772
  | 12 => 170527224079191030215468941432846946962
  | 13 => 140448249833240228113193675482554442118
  | 14 => 56331898693420419135595831813783177621
  | 15 => 42547498440021841188620561430731564101
  | 16 => 182573700087192995885592109012670087258
  | 17 => 214390612325721019559863610766270943254
  | 18 => 140259535719808574066955194854471526656
  | 19 => 115149616090314425123195322508939773504
  | 20 => 133610987649230586294513905064720098693
  | 21 => 49848121663435677780359791322376185425
  | 22 => 1836249658669552507533222541429064072
  | 23 => 173215390862136907770605517106739192912
  | 24 => 90560675098110267033839848993986793750
  | 25 => 85577187065045653950764877966807221606
  | 26 => 1
  | _ => 0

def vectorCode (code : ℕ) (i : Fin 64) : ZMod 3 := packedDigit 2 code i.val

def vectors (i : Fin 14) : V := vectorCode (stageCode (2*i.val))
def middle (i : Fin 13) : V := vectorCode (stageCode (2*i.val+1))

private def rowAt (b j : Fin 8) : Fin 64 := ⟨8*b.val+j.val,by omega⟩
private theorem rowAt_surjective (i : Fin 64) : ∃ b j : Fin 8, rowAt b j=i := by
  refine ⟨⟨i.val/8,by omega⟩,⟨i.val%8,by omega⟩,?_⟩
  apply Fin.ext
  change 8*(i.val/8)+i.val%8=i.val
  omega

private theorem packed_step_0_block_0 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 0 j).val) (stageCode 0) 64 % 3=
      packedDigit 2 (stageCode 1) (rowAt 0 j).val % 3 := by
  decide +kernel

private theorem packed_step_0_block_1 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 1 j).val) (stageCode 0) 64 % 3=
      packedDigit 2 (stageCode 1) (rowAt 1 j).val % 3 := by
  decide +kernel

private theorem packed_step_0_block_2 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 2 j).val) (stageCode 0) 64 % 3=
      packedDigit 2 (stageCode 1) (rowAt 2 j).val % 3 := by
  decide +kernel

private theorem packed_step_0_block_3 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 3 j).val) (stageCode 0) 64 % 3=
      packedDigit 2 (stageCode 1) (rowAt 3 j).val % 3 := by
  decide +kernel

private theorem packed_step_0_block_4 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 4 j).val) (stageCode 0) 64 % 3=
      packedDigit 2 (stageCode 1) (rowAt 4 j).val % 3 := by
  decide +kernel

private theorem packed_step_0_block_5 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 5 j).val) (stageCode 0) 64 % 3=
      packedDigit 2 (stageCode 1) (rowAt 5 j).val % 3 := by
  decide +kernel

private theorem packed_step_0_block_6 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 6 j).val) (stageCode 0) 64 % 3=
      packedDigit 2 (stageCode 1) (rowAt 6 j).val % 3 := by
  decide +kernel

private theorem packed_step_0_block_7 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 7 j).val) (stageCode 0) 64 % 3=
      packedDigit 2 (stageCode 1) (rowAt 7 j).val % 3 := by
  decide +kernel

theorem packed_step_0 (z : Fin 64) :
    packedDot 2 (secondRowCode z.val) (stageCode 0) 64 % 3=
      packedDigit 2 (stageCode 1) z.val % 3 := by
  obtain ⟨b,j,rfl⟩ := rowAt_surjective z
  fin_cases b
  · exact packed_step_0_block_0 j
  · exact packed_step_0_block_1 j
  · exact packed_step_0_block_2 j
  · exact packed_step_0_block_3 j
  · exact packed_step_0_block_4 j
  · exact packed_step_0_block_5 j
  · exact packed_step_0_block_6 j
  · exact packed_step_0_block_7 j

private theorem packed_step_1_block_0 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 0 j).val) (stageCode 1) 64 % 3=
      packedDigit 2 (stageCode 2) (rowAt 0 j).val % 3 := by
  decide +kernel

private theorem packed_step_1_block_1 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 1 j).val) (stageCode 1) 64 % 3=
      packedDigit 2 (stageCode 2) (rowAt 1 j).val % 3 := by
  decide +kernel

private theorem packed_step_1_block_2 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 2 j).val) (stageCode 1) 64 % 3=
      packedDigit 2 (stageCode 2) (rowAt 2 j).val % 3 := by
  decide +kernel

private theorem packed_step_1_block_3 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 3 j).val) (stageCode 1) 64 % 3=
      packedDigit 2 (stageCode 2) (rowAt 3 j).val % 3 := by
  decide +kernel

private theorem packed_step_1_block_4 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 4 j).val) (stageCode 1) 64 % 3=
      packedDigit 2 (stageCode 2) (rowAt 4 j).val % 3 := by
  decide +kernel

private theorem packed_step_1_block_5 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 5 j).val) (stageCode 1) 64 % 3=
      packedDigit 2 (stageCode 2) (rowAt 5 j).val % 3 := by
  decide +kernel

private theorem packed_step_1_block_6 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 6 j).val) (stageCode 1) 64 % 3=
      packedDigit 2 (stageCode 2) (rowAt 6 j).val % 3 := by
  decide +kernel

private theorem packed_step_1_block_7 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 7 j).val) (stageCode 1) 64 % 3=
      packedDigit 2 (stageCode 2) (rowAt 7 j).val % 3 := by
  decide +kernel

theorem packed_step_1 (z : Fin 64) :
    packedDot 2 (firstRowCode z.val) (stageCode 1) 64 % 3=
      packedDigit 2 (stageCode 2) z.val % 3 := by
  obtain ⟨b,j,rfl⟩ := rowAt_surjective z
  fin_cases b
  · exact packed_step_1_block_0 j
  · exact packed_step_1_block_1 j
  · exact packed_step_1_block_2 j
  · exact packed_step_1_block_3 j
  · exact packed_step_1_block_4 j
  · exact packed_step_1_block_5 j
  · exact packed_step_1_block_6 j
  · exact packed_step_1_block_7 j

private theorem packed_step_2_block_0 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 0 j).val) (stageCode 2) 64 % 3=
      packedDigit 2 (stageCode 3) (rowAt 0 j).val % 3 := by
  decide +kernel

private theorem packed_step_2_block_1 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 1 j).val) (stageCode 2) 64 % 3=
      packedDigit 2 (stageCode 3) (rowAt 1 j).val % 3 := by
  decide +kernel

private theorem packed_step_2_block_2 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 2 j).val) (stageCode 2) 64 % 3=
      packedDigit 2 (stageCode 3) (rowAt 2 j).val % 3 := by
  decide +kernel

private theorem packed_step_2_block_3 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 3 j).val) (stageCode 2) 64 % 3=
      packedDigit 2 (stageCode 3) (rowAt 3 j).val % 3 := by
  decide +kernel

private theorem packed_step_2_block_4 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 4 j).val) (stageCode 2) 64 % 3=
      packedDigit 2 (stageCode 3) (rowAt 4 j).val % 3 := by
  decide +kernel

private theorem packed_step_2_block_5 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 5 j).val) (stageCode 2) 64 % 3=
      packedDigit 2 (stageCode 3) (rowAt 5 j).val % 3 := by
  decide +kernel

private theorem packed_step_2_block_6 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 6 j).val) (stageCode 2) 64 % 3=
      packedDigit 2 (stageCode 3) (rowAt 6 j).val % 3 := by
  decide +kernel

private theorem packed_step_2_block_7 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 7 j).val) (stageCode 2) 64 % 3=
      packedDigit 2 (stageCode 3) (rowAt 7 j).val % 3 := by
  decide +kernel

theorem packed_step_2 (z : Fin 64) :
    packedDot 2 (secondRowCode z.val) (stageCode 2) 64 % 3=
      packedDigit 2 (stageCode 3) z.val % 3 := by
  obtain ⟨b,j,rfl⟩ := rowAt_surjective z
  fin_cases b
  · exact packed_step_2_block_0 j
  · exact packed_step_2_block_1 j
  · exact packed_step_2_block_2 j
  · exact packed_step_2_block_3 j
  · exact packed_step_2_block_4 j
  · exact packed_step_2_block_5 j
  · exact packed_step_2_block_6 j
  · exact packed_step_2_block_7 j

private theorem packed_step_3_block_0 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 0 j).val) (stageCode 3) 64 % 3=
      packedDigit 2 (stageCode 4) (rowAt 0 j).val % 3 := by
  decide +kernel

private theorem packed_step_3_block_1 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 1 j).val) (stageCode 3) 64 % 3=
      packedDigit 2 (stageCode 4) (rowAt 1 j).val % 3 := by
  decide +kernel

private theorem packed_step_3_block_2 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 2 j).val) (stageCode 3) 64 % 3=
      packedDigit 2 (stageCode 4) (rowAt 2 j).val % 3 := by
  decide +kernel

private theorem packed_step_3_block_3 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 3 j).val) (stageCode 3) 64 % 3=
      packedDigit 2 (stageCode 4) (rowAt 3 j).val % 3 := by
  decide +kernel

private theorem packed_step_3_block_4 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 4 j).val) (stageCode 3) 64 % 3=
      packedDigit 2 (stageCode 4) (rowAt 4 j).val % 3 := by
  decide +kernel

private theorem packed_step_3_block_5 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 5 j).val) (stageCode 3) 64 % 3=
      packedDigit 2 (stageCode 4) (rowAt 5 j).val % 3 := by
  decide +kernel

private theorem packed_step_3_block_6 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 6 j).val) (stageCode 3) 64 % 3=
      packedDigit 2 (stageCode 4) (rowAt 6 j).val % 3 := by
  decide +kernel

private theorem packed_step_3_block_7 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 7 j).val) (stageCode 3) 64 % 3=
      packedDigit 2 (stageCode 4) (rowAt 7 j).val % 3 := by
  decide +kernel

theorem packed_step_3 (z : Fin 64) :
    packedDot 2 (firstRowCode z.val) (stageCode 3) 64 % 3=
      packedDigit 2 (stageCode 4) z.val % 3 := by
  obtain ⟨b,j,rfl⟩ := rowAt_surjective z
  fin_cases b
  · exact packed_step_3_block_0 j
  · exact packed_step_3_block_1 j
  · exact packed_step_3_block_2 j
  · exact packed_step_3_block_3 j
  · exact packed_step_3_block_4 j
  · exact packed_step_3_block_5 j
  · exact packed_step_3_block_6 j
  · exact packed_step_3_block_7 j

private theorem packed_step_4_block_0 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 0 j).val) (stageCode 4) 64 % 3=
      packedDigit 2 (stageCode 5) (rowAt 0 j).val % 3 := by
  decide +kernel

private theorem packed_step_4_block_1 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 1 j).val) (stageCode 4) 64 % 3=
      packedDigit 2 (stageCode 5) (rowAt 1 j).val % 3 := by
  decide +kernel

private theorem packed_step_4_block_2 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 2 j).val) (stageCode 4) 64 % 3=
      packedDigit 2 (stageCode 5) (rowAt 2 j).val % 3 := by
  decide +kernel

private theorem packed_step_4_block_3 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 3 j).val) (stageCode 4) 64 % 3=
      packedDigit 2 (stageCode 5) (rowAt 3 j).val % 3 := by
  decide +kernel

private theorem packed_step_4_block_4 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 4 j).val) (stageCode 4) 64 % 3=
      packedDigit 2 (stageCode 5) (rowAt 4 j).val % 3 := by
  decide +kernel

private theorem packed_step_4_block_5 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 5 j).val) (stageCode 4) 64 % 3=
      packedDigit 2 (stageCode 5) (rowAt 5 j).val % 3 := by
  decide +kernel

private theorem packed_step_4_block_6 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 6 j).val) (stageCode 4) 64 % 3=
      packedDigit 2 (stageCode 5) (rowAt 6 j).val % 3 := by
  decide +kernel

private theorem packed_step_4_block_7 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 7 j).val) (stageCode 4) 64 % 3=
      packedDigit 2 (stageCode 5) (rowAt 7 j).val % 3 := by
  decide +kernel

theorem packed_step_4 (z : Fin 64) :
    packedDot 2 (secondRowCode z.val) (stageCode 4) 64 % 3=
      packedDigit 2 (stageCode 5) z.val % 3 := by
  obtain ⟨b,j,rfl⟩ := rowAt_surjective z
  fin_cases b
  · exact packed_step_4_block_0 j
  · exact packed_step_4_block_1 j
  · exact packed_step_4_block_2 j
  · exact packed_step_4_block_3 j
  · exact packed_step_4_block_4 j
  · exact packed_step_4_block_5 j
  · exact packed_step_4_block_6 j
  · exact packed_step_4_block_7 j

private theorem packed_step_5_block_0 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 0 j).val) (stageCode 5) 64 % 3=
      packedDigit 2 (stageCode 6) (rowAt 0 j).val % 3 := by
  decide +kernel

private theorem packed_step_5_block_1 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 1 j).val) (stageCode 5) 64 % 3=
      packedDigit 2 (stageCode 6) (rowAt 1 j).val % 3 := by
  decide +kernel

private theorem packed_step_5_block_2 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 2 j).val) (stageCode 5) 64 % 3=
      packedDigit 2 (stageCode 6) (rowAt 2 j).val % 3 := by
  decide +kernel

private theorem packed_step_5_block_3 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 3 j).val) (stageCode 5) 64 % 3=
      packedDigit 2 (stageCode 6) (rowAt 3 j).val % 3 := by
  decide +kernel

private theorem packed_step_5_block_4 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 4 j).val) (stageCode 5) 64 % 3=
      packedDigit 2 (stageCode 6) (rowAt 4 j).val % 3 := by
  decide +kernel

private theorem packed_step_5_block_5 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 5 j).val) (stageCode 5) 64 % 3=
      packedDigit 2 (stageCode 6) (rowAt 5 j).val % 3 := by
  decide +kernel

private theorem packed_step_5_block_6 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 6 j).val) (stageCode 5) 64 % 3=
      packedDigit 2 (stageCode 6) (rowAt 6 j).val % 3 := by
  decide +kernel

private theorem packed_step_5_block_7 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 7 j).val) (stageCode 5) 64 % 3=
      packedDigit 2 (stageCode 6) (rowAt 7 j).val % 3 := by
  decide +kernel

theorem packed_step_5 (z : Fin 64) :
    packedDot 2 (firstRowCode z.val) (stageCode 5) 64 % 3=
      packedDigit 2 (stageCode 6) z.val % 3 := by
  obtain ⟨b,j,rfl⟩ := rowAt_surjective z
  fin_cases b
  · exact packed_step_5_block_0 j
  · exact packed_step_5_block_1 j
  · exact packed_step_5_block_2 j
  · exact packed_step_5_block_3 j
  · exact packed_step_5_block_4 j
  · exact packed_step_5_block_5 j
  · exact packed_step_5_block_6 j
  · exact packed_step_5_block_7 j

private theorem packed_step_6_block_0 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 0 j).val) (stageCode 6) 64 % 3=
      packedDigit 2 (stageCode 7) (rowAt 0 j).val % 3 := by
  decide +kernel

private theorem packed_step_6_block_1 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 1 j).val) (stageCode 6) 64 % 3=
      packedDigit 2 (stageCode 7) (rowAt 1 j).val % 3 := by
  decide +kernel

private theorem packed_step_6_block_2 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 2 j).val) (stageCode 6) 64 % 3=
      packedDigit 2 (stageCode 7) (rowAt 2 j).val % 3 := by
  decide +kernel

private theorem packed_step_6_block_3 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 3 j).val) (stageCode 6) 64 % 3=
      packedDigit 2 (stageCode 7) (rowAt 3 j).val % 3 := by
  decide +kernel

private theorem packed_step_6_block_4 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 4 j).val) (stageCode 6) 64 % 3=
      packedDigit 2 (stageCode 7) (rowAt 4 j).val % 3 := by
  decide +kernel

private theorem packed_step_6_block_5 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 5 j).val) (stageCode 6) 64 % 3=
      packedDigit 2 (stageCode 7) (rowAt 5 j).val % 3 := by
  decide +kernel

private theorem packed_step_6_block_6 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 6 j).val) (stageCode 6) 64 % 3=
      packedDigit 2 (stageCode 7) (rowAt 6 j).val % 3 := by
  decide +kernel

private theorem packed_step_6_block_7 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 7 j).val) (stageCode 6) 64 % 3=
      packedDigit 2 (stageCode 7) (rowAt 7 j).val % 3 := by
  decide +kernel

theorem packed_step_6 (z : Fin 64) :
    packedDot 2 (secondRowCode z.val) (stageCode 6) 64 % 3=
      packedDigit 2 (stageCode 7) z.val % 3 := by
  obtain ⟨b,j,rfl⟩ := rowAt_surjective z
  fin_cases b
  · exact packed_step_6_block_0 j
  · exact packed_step_6_block_1 j
  · exact packed_step_6_block_2 j
  · exact packed_step_6_block_3 j
  · exact packed_step_6_block_4 j
  · exact packed_step_6_block_5 j
  · exact packed_step_6_block_6 j
  · exact packed_step_6_block_7 j

private theorem packed_step_7_block_0 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 0 j).val) (stageCode 7) 64 % 3=
      packedDigit 2 (stageCode 8) (rowAt 0 j).val % 3 := by
  decide +kernel

private theorem packed_step_7_block_1 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 1 j).val) (stageCode 7) 64 % 3=
      packedDigit 2 (stageCode 8) (rowAt 1 j).val % 3 := by
  decide +kernel

private theorem packed_step_7_block_2 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 2 j).val) (stageCode 7) 64 % 3=
      packedDigit 2 (stageCode 8) (rowAt 2 j).val % 3 := by
  decide +kernel

private theorem packed_step_7_block_3 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 3 j).val) (stageCode 7) 64 % 3=
      packedDigit 2 (stageCode 8) (rowAt 3 j).val % 3 := by
  decide +kernel

private theorem packed_step_7_block_4 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 4 j).val) (stageCode 7) 64 % 3=
      packedDigit 2 (stageCode 8) (rowAt 4 j).val % 3 := by
  decide +kernel

private theorem packed_step_7_block_5 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 5 j).val) (stageCode 7) 64 % 3=
      packedDigit 2 (stageCode 8) (rowAt 5 j).val % 3 := by
  decide +kernel

private theorem packed_step_7_block_6 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 6 j).val) (stageCode 7) 64 % 3=
      packedDigit 2 (stageCode 8) (rowAt 6 j).val % 3 := by
  decide +kernel

private theorem packed_step_7_block_7 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 7 j).val) (stageCode 7) 64 % 3=
      packedDigit 2 (stageCode 8) (rowAt 7 j).val % 3 := by
  decide +kernel

theorem packed_step_7 (z : Fin 64) :
    packedDot 2 (firstRowCode z.val) (stageCode 7) 64 % 3=
      packedDigit 2 (stageCode 8) z.val % 3 := by
  obtain ⟨b,j,rfl⟩ := rowAt_surjective z
  fin_cases b
  · exact packed_step_7_block_0 j
  · exact packed_step_7_block_1 j
  · exact packed_step_7_block_2 j
  · exact packed_step_7_block_3 j
  · exact packed_step_7_block_4 j
  · exact packed_step_7_block_5 j
  · exact packed_step_7_block_6 j
  · exact packed_step_7_block_7 j

private theorem packed_step_8_block_0 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 0 j).val) (stageCode 8) 64 % 3=
      packedDigit 2 (stageCode 9) (rowAt 0 j).val % 3 := by
  decide +kernel

private theorem packed_step_8_block_1 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 1 j).val) (stageCode 8) 64 % 3=
      packedDigit 2 (stageCode 9) (rowAt 1 j).val % 3 := by
  decide +kernel

private theorem packed_step_8_block_2 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 2 j).val) (stageCode 8) 64 % 3=
      packedDigit 2 (stageCode 9) (rowAt 2 j).val % 3 := by
  decide +kernel

private theorem packed_step_8_block_3 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 3 j).val) (stageCode 8) 64 % 3=
      packedDigit 2 (stageCode 9) (rowAt 3 j).val % 3 := by
  decide +kernel

private theorem packed_step_8_block_4 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 4 j).val) (stageCode 8) 64 % 3=
      packedDigit 2 (stageCode 9) (rowAt 4 j).val % 3 := by
  decide +kernel

private theorem packed_step_8_block_5 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 5 j).val) (stageCode 8) 64 % 3=
      packedDigit 2 (stageCode 9) (rowAt 5 j).val % 3 := by
  decide +kernel

private theorem packed_step_8_block_6 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 6 j).val) (stageCode 8) 64 % 3=
      packedDigit 2 (stageCode 9) (rowAt 6 j).val % 3 := by
  decide +kernel

private theorem packed_step_8_block_7 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 7 j).val) (stageCode 8) 64 % 3=
      packedDigit 2 (stageCode 9) (rowAt 7 j).val % 3 := by
  decide +kernel

theorem packed_step_8 (z : Fin 64) :
    packedDot 2 (secondRowCode z.val) (stageCode 8) 64 % 3=
      packedDigit 2 (stageCode 9) z.val % 3 := by
  obtain ⟨b,j,rfl⟩ := rowAt_surjective z
  fin_cases b
  · exact packed_step_8_block_0 j
  · exact packed_step_8_block_1 j
  · exact packed_step_8_block_2 j
  · exact packed_step_8_block_3 j
  · exact packed_step_8_block_4 j
  · exact packed_step_8_block_5 j
  · exact packed_step_8_block_6 j
  · exact packed_step_8_block_7 j

private theorem packed_step_9_block_0 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 0 j).val) (stageCode 9) 64 % 3=
      packedDigit 2 (stageCode 10) (rowAt 0 j).val % 3 := by
  decide +kernel

private theorem packed_step_9_block_1 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 1 j).val) (stageCode 9) 64 % 3=
      packedDigit 2 (stageCode 10) (rowAt 1 j).val % 3 := by
  decide +kernel

private theorem packed_step_9_block_2 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 2 j).val) (stageCode 9) 64 % 3=
      packedDigit 2 (stageCode 10) (rowAt 2 j).val % 3 := by
  decide +kernel

private theorem packed_step_9_block_3 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 3 j).val) (stageCode 9) 64 % 3=
      packedDigit 2 (stageCode 10) (rowAt 3 j).val % 3 := by
  decide +kernel

private theorem packed_step_9_block_4 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 4 j).val) (stageCode 9) 64 % 3=
      packedDigit 2 (stageCode 10) (rowAt 4 j).val % 3 := by
  decide +kernel

private theorem packed_step_9_block_5 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 5 j).val) (stageCode 9) 64 % 3=
      packedDigit 2 (stageCode 10) (rowAt 5 j).val % 3 := by
  decide +kernel

private theorem packed_step_9_block_6 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 6 j).val) (stageCode 9) 64 % 3=
      packedDigit 2 (stageCode 10) (rowAt 6 j).val % 3 := by
  decide +kernel

private theorem packed_step_9_block_7 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 7 j).val) (stageCode 9) 64 % 3=
      packedDigit 2 (stageCode 10) (rowAt 7 j).val % 3 := by
  decide +kernel

theorem packed_step_9 (z : Fin 64) :
    packedDot 2 (firstRowCode z.val) (stageCode 9) 64 % 3=
      packedDigit 2 (stageCode 10) z.val % 3 := by
  obtain ⟨b,j,rfl⟩ := rowAt_surjective z
  fin_cases b
  · exact packed_step_9_block_0 j
  · exact packed_step_9_block_1 j
  · exact packed_step_9_block_2 j
  · exact packed_step_9_block_3 j
  · exact packed_step_9_block_4 j
  · exact packed_step_9_block_5 j
  · exact packed_step_9_block_6 j
  · exact packed_step_9_block_7 j

private theorem packed_step_10_block_0 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 0 j).val) (stageCode 10) 64 % 3=
      packedDigit 2 (stageCode 11) (rowAt 0 j).val % 3 := by
  decide +kernel

private theorem packed_step_10_block_1 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 1 j).val) (stageCode 10) 64 % 3=
      packedDigit 2 (stageCode 11) (rowAt 1 j).val % 3 := by
  decide +kernel

private theorem packed_step_10_block_2 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 2 j).val) (stageCode 10) 64 % 3=
      packedDigit 2 (stageCode 11) (rowAt 2 j).val % 3 := by
  decide +kernel

private theorem packed_step_10_block_3 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 3 j).val) (stageCode 10) 64 % 3=
      packedDigit 2 (stageCode 11) (rowAt 3 j).val % 3 := by
  decide +kernel

private theorem packed_step_10_block_4 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 4 j).val) (stageCode 10) 64 % 3=
      packedDigit 2 (stageCode 11) (rowAt 4 j).val % 3 := by
  decide +kernel

private theorem packed_step_10_block_5 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 5 j).val) (stageCode 10) 64 % 3=
      packedDigit 2 (stageCode 11) (rowAt 5 j).val % 3 := by
  decide +kernel

private theorem packed_step_10_block_6 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 6 j).val) (stageCode 10) 64 % 3=
      packedDigit 2 (stageCode 11) (rowAt 6 j).val % 3 := by
  decide +kernel

private theorem packed_step_10_block_7 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 7 j).val) (stageCode 10) 64 % 3=
      packedDigit 2 (stageCode 11) (rowAt 7 j).val % 3 := by
  decide +kernel

theorem packed_step_10 (z : Fin 64) :
    packedDot 2 (secondRowCode z.val) (stageCode 10) 64 % 3=
      packedDigit 2 (stageCode 11) z.val % 3 := by
  obtain ⟨b,j,rfl⟩ := rowAt_surjective z
  fin_cases b
  · exact packed_step_10_block_0 j
  · exact packed_step_10_block_1 j
  · exact packed_step_10_block_2 j
  · exact packed_step_10_block_3 j
  · exact packed_step_10_block_4 j
  · exact packed_step_10_block_5 j
  · exact packed_step_10_block_6 j
  · exact packed_step_10_block_7 j

private theorem packed_step_11_block_0 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 0 j).val) (stageCode 11) 64 % 3=
      packedDigit 2 (stageCode 12) (rowAt 0 j).val % 3 := by
  decide +kernel

private theorem packed_step_11_block_1 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 1 j).val) (stageCode 11) 64 % 3=
      packedDigit 2 (stageCode 12) (rowAt 1 j).val % 3 := by
  decide +kernel

private theorem packed_step_11_block_2 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 2 j).val) (stageCode 11) 64 % 3=
      packedDigit 2 (stageCode 12) (rowAt 2 j).val % 3 := by
  decide +kernel

private theorem packed_step_11_block_3 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 3 j).val) (stageCode 11) 64 % 3=
      packedDigit 2 (stageCode 12) (rowAt 3 j).val % 3 := by
  decide +kernel

private theorem packed_step_11_block_4 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 4 j).val) (stageCode 11) 64 % 3=
      packedDigit 2 (stageCode 12) (rowAt 4 j).val % 3 := by
  decide +kernel

private theorem packed_step_11_block_5 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 5 j).val) (stageCode 11) 64 % 3=
      packedDigit 2 (stageCode 12) (rowAt 5 j).val % 3 := by
  decide +kernel

private theorem packed_step_11_block_6 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 6 j).val) (stageCode 11) 64 % 3=
      packedDigit 2 (stageCode 12) (rowAt 6 j).val % 3 := by
  decide +kernel

private theorem packed_step_11_block_7 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 7 j).val) (stageCode 11) 64 % 3=
      packedDigit 2 (stageCode 12) (rowAt 7 j).val % 3 := by
  decide +kernel

theorem packed_step_11 (z : Fin 64) :
    packedDot 2 (firstRowCode z.val) (stageCode 11) 64 % 3=
      packedDigit 2 (stageCode 12) z.val % 3 := by
  obtain ⟨b,j,rfl⟩ := rowAt_surjective z
  fin_cases b
  · exact packed_step_11_block_0 j
  · exact packed_step_11_block_1 j
  · exact packed_step_11_block_2 j
  · exact packed_step_11_block_3 j
  · exact packed_step_11_block_4 j
  · exact packed_step_11_block_5 j
  · exact packed_step_11_block_6 j
  · exact packed_step_11_block_7 j

private theorem packed_step_12_block_0 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 0 j).val) (stageCode 12) 64 % 3=
      packedDigit 2 (stageCode 13) (rowAt 0 j).val % 3 := by
  decide +kernel

private theorem packed_step_12_block_1 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 1 j).val) (stageCode 12) 64 % 3=
      packedDigit 2 (stageCode 13) (rowAt 1 j).val % 3 := by
  decide +kernel

private theorem packed_step_12_block_2 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 2 j).val) (stageCode 12) 64 % 3=
      packedDigit 2 (stageCode 13) (rowAt 2 j).val % 3 := by
  decide +kernel

private theorem packed_step_12_block_3 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 3 j).val) (stageCode 12) 64 % 3=
      packedDigit 2 (stageCode 13) (rowAt 3 j).val % 3 := by
  decide +kernel

private theorem packed_step_12_block_4 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 4 j).val) (stageCode 12) 64 % 3=
      packedDigit 2 (stageCode 13) (rowAt 4 j).val % 3 := by
  decide +kernel

private theorem packed_step_12_block_5 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 5 j).val) (stageCode 12) 64 % 3=
      packedDigit 2 (stageCode 13) (rowAt 5 j).val % 3 := by
  decide +kernel

private theorem packed_step_12_block_6 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 6 j).val) (stageCode 12) 64 % 3=
      packedDigit 2 (stageCode 13) (rowAt 6 j).val % 3 := by
  decide +kernel

private theorem packed_step_12_block_7 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 7 j).val) (stageCode 12) 64 % 3=
      packedDigit 2 (stageCode 13) (rowAt 7 j).val % 3 := by
  decide +kernel

theorem packed_step_12 (z : Fin 64) :
    packedDot 2 (secondRowCode z.val) (stageCode 12) 64 % 3=
      packedDigit 2 (stageCode 13) z.val % 3 := by
  obtain ⟨b,j,rfl⟩ := rowAt_surjective z
  fin_cases b
  · exact packed_step_12_block_0 j
  · exact packed_step_12_block_1 j
  · exact packed_step_12_block_2 j
  · exact packed_step_12_block_3 j
  · exact packed_step_12_block_4 j
  · exact packed_step_12_block_5 j
  · exact packed_step_12_block_6 j
  · exact packed_step_12_block_7 j

private theorem packed_step_13_block_0 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 0 j).val) (stageCode 13) 64 % 3=
      packedDigit 2 (stageCode 14) (rowAt 0 j).val % 3 := by
  decide +kernel

private theorem packed_step_13_block_1 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 1 j).val) (stageCode 13) 64 % 3=
      packedDigit 2 (stageCode 14) (rowAt 1 j).val % 3 := by
  decide +kernel

private theorem packed_step_13_block_2 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 2 j).val) (stageCode 13) 64 % 3=
      packedDigit 2 (stageCode 14) (rowAt 2 j).val % 3 := by
  decide +kernel

private theorem packed_step_13_block_3 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 3 j).val) (stageCode 13) 64 % 3=
      packedDigit 2 (stageCode 14) (rowAt 3 j).val % 3 := by
  decide +kernel

private theorem packed_step_13_block_4 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 4 j).val) (stageCode 13) 64 % 3=
      packedDigit 2 (stageCode 14) (rowAt 4 j).val % 3 := by
  decide +kernel

private theorem packed_step_13_block_5 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 5 j).val) (stageCode 13) 64 % 3=
      packedDigit 2 (stageCode 14) (rowAt 5 j).val % 3 := by
  decide +kernel

private theorem packed_step_13_block_6 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 6 j).val) (stageCode 13) 64 % 3=
      packedDigit 2 (stageCode 14) (rowAt 6 j).val % 3 := by
  decide +kernel

private theorem packed_step_13_block_7 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 7 j).val) (stageCode 13) 64 % 3=
      packedDigit 2 (stageCode 14) (rowAt 7 j).val % 3 := by
  decide +kernel

theorem packed_step_13 (z : Fin 64) :
    packedDot 2 (firstRowCode z.val) (stageCode 13) 64 % 3=
      packedDigit 2 (stageCode 14) z.val % 3 := by
  obtain ⟨b,j,rfl⟩ := rowAt_surjective z
  fin_cases b
  · exact packed_step_13_block_0 j
  · exact packed_step_13_block_1 j
  · exact packed_step_13_block_2 j
  · exact packed_step_13_block_3 j
  · exact packed_step_13_block_4 j
  · exact packed_step_13_block_5 j
  · exact packed_step_13_block_6 j
  · exact packed_step_13_block_7 j

private theorem packed_step_14_block_0 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 0 j).val) (stageCode 14) 64 % 3=
      packedDigit 2 (stageCode 15) (rowAt 0 j).val % 3 := by
  decide +kernel

private theorem packed_step_14_block_1 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 1 j).val) (stageCode 14) 64 % 3=
      packedDigit 2 (stageCode 15) (rowAt 1 j).val % 3 := by
  decide +kernel

private theorem packed_step_14_block_2 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 2 j).val) (stageCode 14) 64 % 3=
      packedDigit 2 (stageCode 15) (rowAt 2 j).val % 3 := by
  decide +kernel

private theorem packed_step_14_block_3 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 3 j).val) (stageCode 14) 64 % 3=
      packedDigit 2 (stageCode 15) (rowAt 3 j).val % 3 := by
  decide +kernel

private theorem packed_step_14_block_4 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 4 j).val) (stageCode 14) 64 % 3=
      packedDigit 2 (stageCode 15) (rowAt 4 j).val % 3 := by
  decide +kernel

private theorem packed_step_14_block_5 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 5 j).val) (stageCode 14) 64 % 3=
      packedDigit 2 (stageCode 15) (rowAt 5 j).val % 3 := by
  decide +kernel

private theorem packed_step_14_block_6 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 6 j).val) (stageCode 14) 64 % 3=
      packedDigit 2 (stageCode 15) (rowAt 6 j).val % 3 := by
  decide +kernel

private theorem packed_step_14_block_7 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 7 j).val) (stageCode 14) 64 % 3=
      packedDigit 2 (stageCode 15) (rowAt 7 j).val % 3 := by
  decide +kernel

theorem packed_step_14 (z : Fin 64) :
    packedDot 2 (secondRowCode z.val) (stageCode 14) 64 % 3=
      packedDigit 2 (stageCode 15) z.val % 3 := by
  obtain ⟨b,j,rfl⟩ := rowAt_surjective z
  fin_cases b
  · exact packed_step_14_block_0 j
  · exact packed_step_14_block_1 j
  · exact packed_step_14_block_2 j
  · exact packed_step_14_block_3 j
  · exact packed_step_14_block_4 j
  · exact packed_step_14_block_5 j
  · exact packed_step_14_block_6 j
  · exact packed_step_14_block_7 j

private theorem packed_step_15_block_0 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 0 j).val) (stageCode 15) 64 % 3=
      packedDigit 2 (stageCode 16) (rowAt 0 j).val % 3 := by
  decide +kernel

private theorem packed_step_15_block_1 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 1 j).val) (stageCode 15) 64 % 3=
      packedDigit 2 (stageCode 16) (rowAt 1 j).val % 3 := by
  decide +kernel

private theorem packed_step_15_block_2 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 2 j).val) (stageCode 15) 64 % 3=
      packedDigit 2 (stageCode 16) (rowAt 2 j).val % 3 := by
  decide +kernel

private theorem packed_step_15_block_3 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 3 j).val) (stageCode 15) 64 % 3=
      packedDigit 2 (stageCode 16) (rowAt 3 j).val % 3 := by
  decide +kernel

private theorem packed_step_15_block_4 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 4 j).val) (stageCode 15) 64 % 3=
      packedDigit 2 (stageCode 16) (rowAt 4 j).val % 3 := by
  decide +kernel

private theorem packed_step_15_block_5 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 5 j).val) (stageCode 15) 64 % 3=
      packedDigit 2 (stageCode 16) (rowAt 5 j).val % 3 := by
  decide +kernel

private theorem packed_step_15_block_6 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 6 j).val) (stageCode 15) 64 % 3=
      packedDigit 2 (stageCode 16) (rowAt 6 j).val % 3 := by
  decide +kernel

private theorem packed_step_15_block_7 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 7 j).val) (stageCode 15) 64 % 3=
      packedDigit 2 (stageCode 16) (rowAt 7 j).val % 3 := by
  decide +kernel

theorem packed_step_15 (z : Fin 64) :
    packedDot 2 (firstRowCode z.val) (stageCode 15) 64 % 3=
      packedDigit 2 (stageCode 16) z.val % 3 := by
  obtain ⟨b,j,rfl⟩ := rowAt_surjective z
  fin_cases b
  · exact packed_step_15_block_0 j
  · exact packed_step_15_block_1 j
  · exact packed_step_15_block_2 j
  · exact packed_step_15_block_3 j
  · exact packed_step_15_block_4 j
  · exact packed_step_15_block_5 j
  · exact packed_step_15_block_6 j
  · exact packed_step_15_block_7 j

private theorem packed_step_16_block_0 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 0 j).val) (stageCode 16) 64 % 3=
      packedDigit 2 (stageCode 17) (rowAt 0 j).val % 3 := by
  decide +kernel

private theorem packed_step_16_block_1 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 1 j).val) (stageCode 16) 64 % 3=
      packedDigit 2 (stageCode 17) (rowAt 1 j).val % 3 := by
  decide +kernel

private theorem packed_step_16_block_2 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 2 j).val) (stageCode 16) 64 % 3=
      packedDigit 2 (stageCode 17) (rowAt 2 j).val % 3 := by
  decide +kernel

private theorem packed_step_16_block_3 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 3 j).val) (stageCode 16) 64 % 3=
      packedDigit 2 (stageCode 17) (rowAt 3 j).val % 3 := by
  decide +kernel

private theorem packed_step_16_block_4 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 4 j).val) (stageCode 16) 64 % 3=
      packedDigit 2 (stageCode 17) (rowAt 4 j).val % 3 := by
  decide +kernel

private theorem packed_step_16_block_5 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 5 j).val) (stageCode 16) 64 % 3=
      packedDigit 2 (stageCode 17) (rowAt 5 j).val % 3 := by
  decide +kernel

private theorem packed_step_16_block_6 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 6 j).val) (stageCode 16) 64 % 3=
      packedDigit 2 (stageCode 17) (rowAt 6 j).val % 3 := by
  decide +kernel

private theorem packed_step_16_block_7 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 7 j).val) (stageCode 16) 64 % 3=
      packedDigit 2 (stageCode 17) (rowAt 7 j).val % 3 := by
  decide +kernel

theorem packed_step_16 (z : Fin 64) :
    packedDot 2 (secondRowCode z.val) (stageCode 16) 64 % 3=
      packedDigit 2 (stageCode 17) z.val % 3 := by
  obtain ⟨b,j,rfl⟩ := rowAt_surjective z
  fin_cases b
  · exact packed_step_16_block_0 j
  · exact packed_step_16_block_1 j
  · exact packed_step_16_block_2 j
  · exact packed_step_16_block_3 j
  · exact packed_step_16_block_4 j
  · exact packed_step_16_block_5 j
  · exact packed_step_16_block_6 j
  · exact packed_step_16_block_7 j

private theorem packed_step_17_block_0 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 0 j).val) (stageCode 17) 64 % 3=
      packedDigit 2 (stageCode 18) (rowAt 0 j).val % 3 := by
  decide +kernel

private theorem packed_step_17_block_1 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 1 j).val) (stageCode 17) 64 % 3=
      packedDigit 2 (stageCode 18) (rowAt 1 j).val % 3 := by
  decide +kernel

private theorem packed_step_17_block_2 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 2 j).val) (stageCode 17) 64 % 3=
      packedDigit 2 (stageCode 18) (rowAt 2 j).val % 3 := by
  decide +kernel

private theorem packed_step_17_block_3 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 3 j).val) (stageCode 17) 64 % 3=
      packedDigit 2 (stageCode 18) (rowAt 3 j).val % 3 := by
  decide +kernel

private theorem packed_step_17_block_4 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 4 j).val) (stageCode 17) 64 % 3=
      packedDigit 2 (stageCode 18) (rowAt 4 j).val % 3 := by
  decide +kernel

private theorem packed_step_17_block_5 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 5 j).val) (stageCode 17) 64 % 3=
      packedDigit 2 (stageCode 18) (rowAt 5 j).val % 3 := by
  decide +kernel

private theorem packed_step_17_block_6 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 6 j).val) (stageCode 17) 64 % 3=
      packedDigit 2 (stageCode 18) (rowAt 6 j).val % 3 := by
  decide +kernel

private theorem packed_step_17_block_7 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 7 j).val) (stageCode 17) 64 % 3=
      packedDigit 2 (stageCode 18) (rowAt 7 j).val % 3 := by
  decide +kernel

theorem packed_step_17 (z : Fin 64) :
    packedDot 2 (firstRowCode z.val) (stageCode 17) 64 % 3=
      packedDigit 2 (stageCode 18) z.val % 3 := by
  obtain ⟨b,j,rfl⟩ := rowAt_surjective z
  fin_cases b
  · exact packed_step_17_block_0 j
  · exact packed_step_17_block_1 j
  · exact packed_step_17_block_2 j
  · exact packed_step_17_block_3 j
  · exact packed_step_17_block_4 j
  · exact packed_step_17_block_5 j
  · exact packed_step_17_block_6 j
  · exact packed_step_17_block_7 j

private theorem packed_step_18_block_0 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 0 j).val) (stageCode 18) 64 % 3=
      packedDigit 2 (stageCode 19) (rowAt 0 j).val % 3 := by
  decide +kernel

private theorem packed_step_18_block_1 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 1 j).val) (stageCode 18) 64 % 3=
      packedDigit 2 (stageCode 19) (rowAt 1 j).val % 3 := by
  decide +kernel

private theorem packed_step_18_block_2 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 2 j).val) (stageCode 18) 64 % 3=
      packedDigit 2 (stageCode 19) (rowAt 2 j).val % 3 := by
  decide +kernel

private theorem packed_step_18_block_3 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 3 j).val) (stageCode 18) 64 % 3=
      packedDigit 2 (stageCode 19) (rowAt 3 j).val % 3 := by
  decide +kernel

private theorem packed_step_18_block_4 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 4 j).val) (stageCode 18) 64 % 3=
      packedDigit 2 (stageCode 19) (rowAt 4 j).val % 3 := by
  decide +kernel

private theorem packed_step_18_block_5 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 5 j).val) (stageCode 18) 64 % 3=
      packedDigit 2 (stageCode 19) (rowAt 5 j).val % 3 := by
  decide +kernel

private theorem packed_step_18_block_6 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 6 j).val) (stageCode 18) 64 % 3=
      packedDigit 2 (stageCode 19) (rowAt 6 j).val % 3 := by
  decide +kernel

private theorem packed_step_18_block_7 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 7 j).val) (stageCode 18) 64 % 3=
      packedDigit 2 (stageCode 19) (rowAt 7 j).val % 3 := by
  decide +kernel

theorem packed_step_18 (z : Fin 64) :
    packedDot 2 (secondRowCode z.val) (stageCode 18) 64 % 3=
      packedDigit 2 (stageCode 19) z.val % 3 := by
  obtain ⟨b,j,rfl⟩ := rowAt_surjective z
  fin_cases b
  · exact packed_step_18_block_0 j
  · exact packed_step_18_block_1 j
  · exact packed_step_18_block_2 j
  · exact packed_step_18_block_3 j
  · exact packed_step_18_block_4 j
  · exact packed_step_18_block_5 j
  · exact packed_step_18_block_6 j
  · exact packed_step_18_block_7 j

private theorem packed_step_19_block_0 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 0 j).val) (stageCode 19) 64 % 3=
      packedDigit 2 (stageCode 20) (rowAt 0 j).val % 3 := by
  decide +kernel

private theorem packed_step_19_block_1 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 1 j).val) (stageCode 19) 64 % 3=
      packedDigit 2 (stageCode 20) (rowAt 1 j).val % 3 := by
  decide +kernel

private theorem packed_step_19_block_2 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 2 j).val) (stageCode 19) 64 % 3=
      packedDigit 2 (stageCode 20) (rowAt 2 j).val % 3 := by
  decide +kernel

private theorem packed_step_19_block_3 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 3 j).val) (stageCode 19) 64 % 3=
      packedDigit 2 (stageCode 20) (rowAt 3 j).val % 3 := by
  decide +kernel

private theorem packed_step_19_block_4 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 4 j).val) (stageCode 19) 64 % 3=
      packedDigit 2 (stageCode 20) (rowAt 4 j).val % 3 := by
  decide +kernel

private theorem packed_step_19_block_5 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 5 j).val) (stageCode 19) 64 % 3=
      packedDigit 2 (stageCode 20) (rowAt 5 j).val % 3 := by
  decide +kernel

private theorem packed_step_19_block_6 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 6 j).val) (stageCode 19) 64 % 3=
      packedDigit 2 (stageCode 20) (rowAt 6 j).val % 3 := by
  decide +kernel

private theorem packed_step_19_block_7 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 7 j).val) (stageCode 19) 64 % 3=
      packedDigit 2 (stageCode 20) (rowAt 7 j).val % 3 := by
  decide +kernel

theorem packed_step_19 (z : Fin 64) :
    packedDot 2 (firstRowCode z.val) (stageCode 19) 64 % 3=
      packedDigit 2 (stageCode 20) z.val % 3 := by
  obtain ⟨b,j,rfl⟩ := rowAt_surjective z
  fin_cases b
  · exact packed_step_19_block_0 j
  · exact packed_step_19_block_1 j
  · exact packed_step_19_block_2 j
  · exact packed_step_19_block_3 j
  · exact packed_step_19_block_4 j
  · exact packed_step_19_block_5 j
  · exact packed_step_19_block_6 j
  · exact packed_step_19_block_7 j

private theorem packed_step_20_block_0 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 0 j).val) (stageCode 20) 64 % 3=
      packedDigit 2 (stageCode 21) (rowAt 0 j).val % 3 := by
  decide +kernel

private theorem packed_step_20_block_1 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 1 j).val) (stageCode 20) 64 % 3=
      packedDigit 2 (stageCode 21) (rowAt 1 j).val % 3 := by
  decide +kernel

private theorem packed_step_20_block_2 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 2 j).val) (stageCode 20) 64 % 3=
      packedDigit 2 (stageCode 21) (rowAt 2 j).val % 3 := by
  decide +kernel

private theorem packed_step_20_block_3 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 3 j).val) (stageCode 20) 64 % 3=
      packedDigit 2 (stageCode 21) (rowAt 3 j).val % 3 := by
  decide +kernel

private theorem packed_step_20_block_4 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 4 j).val) (stageCode 20) 64 % 3=
      packedDigit 2 (stageCode 21) (rowAt 4 j).val % 3 := by
  decide +kernel

private theorem packed_step_20_block_5 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 5 j).val) (stageCode 20) 64 % 3=
      packedDigit 2 (stageCode 21) (rowAt 5 j).val % 3 := by
  decide +kernel

private theorem packed_step_20_block_6 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 6 j).val) (stageCode 20) 64 % 3=
      packedDigit 2 (stageCode 21) (rowAt 6 j).val % 3 := by
  decide +kernel

private theorem packed_step_20_block_7 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 7 j).val) (stageCode 20) 64 % 3=
      packedDigit 2 (stageCode 21) (rowAt 7 j).val % 3 := by
  decide +kernel

theorem packed_step_20 (z : Fin 64) :
    packedDot 2 (secondRowCode z.val) (stageCode 20) 64 % 3=
      packedDigit 2 (stageCode 21) z.val % 3 := by
  obtain ⟨b,j,rfl⟩ := rowAt_surjective z
  fin_cases b
  · exact packed_step_20_block_0 j
  · exact packed_step_20_block_1 j
  · exact packed_step_20_block_2 j
  · exact packed_step_20_block_3 j
  · exact packed_step_20_block_4 j
  · exact packed_step_20_block_5 j
  · exact packed_step_20_block_6 j
  · exact packed_step_20_block_7 j

private theorem packed_step_21_block_0 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 0 j).val) (stageCode 21) 64 % 3=
      packedDigit 2 (stageCode 22) (rowAt 0 j).val % 3 := by
  decide +kernel

private theorem packed_step_21_block_1 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 1 j).val) (stageCode 21) 64 % 3=
      packedDigit 2 (stageCode 22) (rowAt 1 j).val % 3 := by
  decide +kernel

private theorem packed_step_21_block_2 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 2 j).val) (stageCode 21) 64 % 3=
      packedDigit 2 (stageCode 22) (rowAt 2 j).val % 3 := by
  decide +kernel

private theorem packed_step_21_block_3 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 3 j).val) (stageCode 21) 64 % 3=
      packedDigit 2 (stageCode 22) (rowAt 3 j).val % 3 := by
  decide +kernel

private theorem packed_step_21_block_4 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 4 j).val) (stageCode 21) 64 % 3=
      packedDigit 2 (stageCode 22) (rowAt 4 j).val % 3 := by
  decide +kernel

private theorem packed_step_21_block_5 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 5 j).val) (stageCode 21) 64 % 3=
      packedDigit 2 (stageCode 22) (rowAt 5 j).val % 3 := by
  decide +kernel

private theorem packed_step_21_block_6 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 6 j).val) (stageCode 21) 64 % 3=
      packedDigit 2 (stageCode 22) (rowAt 6 j).val % 3 := by
  decide +kernel

private theorem packed_step_21_block_7 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 7 j).val) (stageCode 21) 64 % 3=
      packedDigit 2 (stageCode 22) (rowAt 7 j).val % 3 := by
  decide +kernel

theorem packed_step_21 (z : Fin 64) :
    packedDot 2 (firstRowCode z.val) (stageCode 21) 64 % 3=
      packedDigit 2 (stageCode 22) z.val % 3 := by
  obtain ⟨b,j,rfl⟩ := rowAt_surjective z
  fin_cases b
  · exact packed_step_21_block_0 j
  · exact packed_step_21_block_1 j
  · exact packed_step_21_block_2 j
  · exact packed_step_21_block_3 j
  · exact packed_step_21_block_4 j
  · exact packed_step_21_block_5 j
  · exact packed_step_21_block_6 j
  · exact packed_step_21_block_7 j

private theorem packed_step_22_block_0 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 0 j).val) (stageCode 22) 64 % 3=
      packedDigit 2 (stageCode 23) (rowAt 0 j).val % 3 := by
  decide +kernel

private theorem packed_step_22_block_1 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 1 j).val) (stageCode 22) 64 % 3=
      packedDigit 2 (stageCode 23) (rowAt 1 j).val % 3 := by
  decide +kernel

private theorem packed_step_22_block_2 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 2 j).val) (stageCode 22) 64 % 3=
      packedDigit 2 (stageCode 23) (rowAt 2 j).val % 3 := by
  decide +kernel

private theorem packed_step_22_block_3 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 3 j).val) (stageCode 22) 64 % 3=
      packedDigit 2 (stageCode 23) (rowAt 3 j).val % 3 := by
  decide +kernel

private theorem packed_step_22_block_4 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 4 j).val) (stageCode 22) 64 % 3=
      packedDigit 2 (stageCode 23) (rowAt 4 j).val % 3 := by
  decide +kernel

private theorem packed_step_22_block_5 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 5 j).val) (stageCode 22) 64 % 3=
      packedDigit 2 (stageCode 23) (rowAt 5 j).val % 3 := by
  decide +kernel

private theorem packed_step_22_block_6 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 6 j).val) (stageCode 22) 64 % 3=
      packedDigit 2 (stageCode 23) (rowAt 6 j).val % 3 := by
  decide +kernel

private theorem packed_step_22_block_7 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 7 j).val) (stageCode 22) 64 % 3=
      packedDigit 2 (stageCode 23) (rowAt 7 j).val % 3 := by
  decide +kernel

theorem packed_step_22 (z : Fin 64) :
    packedDot 2 (secondRowCode z.val) (stageCode 22) 64 % 3=
      packedDigit 2 (stageCode 23) z.val % 3 := by
  obtain ⟨b,j,rfl⟩ := rowAt_surjective z
  fin_cases b
  · exact packed_step_22_block_0 j
  · exact packed_step_22_block_1 j
  · exact packed_step_22_block_2 j
  · exact packed_step_22_block_3 j
  · exact packed_step_22_block_4 j
  · exact packed_step_22_block_5 j
  · exact packed_step_22_block_6 j
  · exact packed_step_22_block_7 j

private theorem packed_step_23_block_0 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 0 j).val) (stageCode 23) 64 % 3=
      packedDigit 2 (stageCode 24) (rowAt 0 j).val % 3 := by
  decide +kernel

private theorem packed_step_23_block_1 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 1 j).val) (stageCode 23) 64 % 3=
      packedDigit 2 (stageCode 24) (rowAt 1 j).val % 3 := by
  decide +kernel

private theorem packed_step_23_block_2 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 2 j).val) (stageCode 23) 64 % 3=
      packedDigit 2 (stageCode 24) (rowAt 2 j).val % 3 := by
  decide +kernel

private theorem packed_step_23_block_3 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 3 j).val) (stageCode 23) 64 % 3=
      packedDigit 2 (stageCode 24) (rowAt 3 j).val % 3 := by
  decide +kernel

private theorem packed_step_23_block_4 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 4 j).val) (stageCode 23) 64 % 3=
      packedDigit 2 (stageCode 24) (rowAt 4 j).val % 3 := by
  decide +kernel

private theorem packed_step_23_block_5 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 5 j).val) (stageCode 23) 64 % 3=
      packedDigit 2 (stageCode 24) (rowAt 5 j).val % 3 := by
  decide +kernel

private theorem packed_step_23_block_6 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 6 j).val) (stageCode 23) 64 % 3=
      packedDigit 2 (stageCode 24) (rowAt 6 j).val % 3 := by
  decide +kernel

private theorem packed_step_23_block_7 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 7 j).val) (stageCode 23) 64 % 3=
      packedDigit 2 (stageCode 24) (rowAt 7 j).val % 3 := by
  decide +kernel

theorem packed_step_23 (z : Fin 64) :
    packedDot 2 (firstRowCode z.val) (stageCode 23) 64 % 3=
      packedDigit 2 (stageCode 24) z.val % 3 := by
  obtain ⟨b,j,rfl⟩ := rowAt_surjective z
  fin_cases b
  · exact packed_step_23_block_0 j
  · exact packed_step_23_block_1 j
  · exact packed_step_23_block_2 j
  · exact packed_step_23_block_3 j
  · exact packed_step_23_block_4 j
  · exact packed_step_23_block_5 j
  · exact packed_step_23_block_6 j
  · exact packed_step_23_block_7 j

private theorem packed_step_24_block_0 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 0 j).val) (stageCode 24) 64 % 3=
      packedDigit 2 (stageCode 25) (rowAt 0 j).val % 3 := by
  decide +kernel

private theorem packed_step_24_block_1 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 1 j).val) (stageCode 24) 64 % 3=
      packedDigit 2 (stageCode 25) (rowAt 1 j).val % 3 := by
  decide +kernel

private theorem packed_step_24_block_2 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 2 j).val) (stageCode 24) 64 % 3=
      packedDigit 2 (stageCode 25) (rowAt 2 j).val % 3 := by
  decide +kernel

private theorem packed_step_24_block_3 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 3 j).val) (stageCode 24) 64 % 3=
      packedDigit 2 (stageCode 25) (rowAt 3 j).val % 3 := by
  decide +kernel

private theorem packed_step_24_block_4 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 4 j).val) (stageCode 24) 64 % 3=
      packedDigit 2 (stageCode 25) (rowAt 4 j).val % 3 := by
  decide +kernel

private theorem packed_step_24_block_5 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 5 j).val) (stageCode 24) 64 % 3=
      packedDigit 2 (stageCode 25) (rowAt 5 j).val % 3 := by
  decide +kernel

private theorem packed_step_24_block_6 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 6 j).val) (stageCode 24) 64 % 3=
      packedDigit 2 (stageCode 25) (rowAt 6 j).val % 3 := by
  decide +kernel

private theorem packed_step_24_block_7 : ∀ j : Fin 8,
    packedDot 2 (secondRowCode (rowAt 7 j).val) (stageCode 24) 64 % 3=
      packedDigit 2 (stageCode 25) (rowAt 7 j).val % 3 := by
  decide +kernel

theorem packed_step_24 (z : Fin 64) :
    packedDot 2 (secondRowCode z.val) (stageCode 24) 64 % 3=
      packedDigit 2 (stageCode 25) z.val % 3 := by
  obtain ⟨b,j,rfl⟩ := rowAt_surjective z
  fin_cases b
  · exact packed_step_24_block_0 j
  · exact packed_step_24_block_1 j
  · exact packed_step_24_block_2 j
  · exact packed_step_24_block_3 j
  · exact packed_step_24_block_4 j
  · exact packed_step_24_block_5 j
  · exact packed_step_24_block_6 j
  · exact packed_step_24_block_7 j

private theorem packed_step_25_block_0 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 0 j).val) (stageCode 25) 64 % 3=
      packedDigit 2 (stageCode 26) (rowAt 0 j).val % 3 := by
  decide +kernel

private theorem packed_step_25_block_1 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 1 j).val) (stageCode 25) 64 % 3=
      packedDigit 2 (stageCode 26) (rowAt 1 j).val % 3 := by
  decide +kernel

private theorem packed_step_25_block_2 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 2 j).val) (stageCode 25) 64 % 3=
      packedDigit 2 (stageCode 26) (rowAt 2 j).val % 3 := by
  decide +kernel

private theorem packed_step_25_block_3 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 3 j).val) (stageCode 25) 64 % 3=
      packedDigit 2 (stageCode 26) (rowAt 3 j).val % 3 := by
  decide +kernel

private theorem packed_step_25_block_4 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 4 j).val) (stageCode 25) 64 % 3=
      packedDigit 2 (stageCode 26) (rowAt 4 j).val % 3 := by
  decide +kernel

private theorem packed_step_25_block_5 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 5 j).val) (stageCode 25) 64 % 3=
      packedDigit 2 (stageCode 26) (rowAt 5 j).val % 3 := by
  decide +kernel

private theorem packed_step_25_block_6 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 6 j).val) (stageCode 25) 64 % 3=
      packedDigit 2 (stageCode 26) (rowAt 6 j).val % 3 := by
  decide +kernel

private theorem packed_step_25_block_7 : ∀ j : Fin 8,
    packedDot 2 (firstRowCode (rowAt 7 j).val) (stageCode 25) 64 % 3=
      packedDigit 2 (stageCode 26) (rowAt 7 j).val % 3 := by
  decide +kernel

theorem packed_step_25 (z : Fin 64) :
    packedDot 2 (firstRowCode z.val) (stageCode 25) 64 % 3=
      packedDigit 2 (stageCode 26) z.val % 3 := by
  obtain ⟨b,j,rfl⟩ := rowAt_surjective z
  fin_cases b
  · exact packed_step_25_block_0 j
  · exact packed_step_25_block_1 j
  · exact packed_step_25_block_2 j
  · exact packed_step_25_block_3 j
  · exact packed_step_25_block_4 j
  · exact packed_step_25_block_5 j
  · exact packed_step_25_block_6 j
  · exact packed_step_25_block_7 j

theorem b_step (i : Fin 13) :
    CFSG.Models.MatrixData.matrix 3 64 rows2 *ᵥ vectors i.castSucc=middle i := by
  apply packed_vector_step 3 64 2 rows2 secondRowCode
    (stageCode (2*i.val)) (stageCode (2*i.val+1)) second_row_binding
  fin_cases i
  · exact packed_step_0
  · exact packed_step_2
  · exact packed_step_4
  · exact packed_step_6
  · exact packed_step_8
  · exact packed_step_10
  · exact packed_step_12
  · exact packed_step_14
  · exact packed_step_16
  · exact packed_step_18
  · exact packed_step_20
  · exact packed_step_22
  · exact packed_step_24

theorem a_step (i : Fin 13) :
    CFSG.Models.MatrixData.matrix 3 64 rows1 *ᵥ middle i=vectors i.succ := by
  change CFSG.Models.MatrixData.matrix 3 64 rows1 *ᵥ vectorCode (stageCode (2*i.val+1))=
    vectorCode (stageCode (2*(i.val+1)))
  have he : 2*(i.val+1)=2*i.val+2 := by omega
  rw [he]
  apply packed_vector_step 3 64 2 rows1 firstRowCode
    (stageCode (2*i.val+1)) (stageCode (2*i.val+2)) first_row_binding
  fin_cases i
  · exact packed_step_1
  · exact packed_step_3
  · exact packed_step_5
  · exact packed_step_7
  · exact packed_step_9
  · exact packed_step_11
  · exact packed_step_13
  · exact packed_step_15
  · exact packed_step_17
  · exact packed_step_19
  · exact packed_step_21
  · exact packed_step_23
  · exact packed_step_25

def wordEnd : Module.End (ZMod 3) V := productEnd 3 64 rows1 rows2

theorem consecutive (i : Fin 13) : wordEnd (vectors i.castSucc)=vectors i.succ := by
  change CFSG.Models.MatrixData.matrix 3 64 rows1 *ᵥ
    (CFSG.Models.MatrixData.matrix 3 64 rows2 *ᵥ vectors i.castSucc)=vectors i.succ
  rw [b_step,a_step]

theorem pow_initial (i : Fin 14) : (wordEnd^i.val) (vectors 0)=vectors i :=
  LinearMapSelectedKrylovPeriod.pow_apply_eq_vector wordEnd 13 vectors consecutive i

theorem return_thirteen : (wordEnd^13) (vectors 0)=vectors 0 := by
  have h : (wordEnd^13) (vectors 0)=vectors 13 := pow_initial ⟨13,by decide⟩
  exact h.trans (show vectors 13=vectors 0 from rfl)

theorem nonreturn_one : wordEnd (vectors 0)≠vectors 0 := by
  have h : wordEnd (vectors 0)=vectors 1 := by simpa only [pow_one] using pow_initial ⟨1,by decide⟩
  have hn : vectors 1 (1 : Fin 64)≠vectors 0 1 := by decide +kernel
  intro he
  exact hn (congrFun (h.symm.trans he) 1)

theorem exists_thirteen_dvd_orderOf (hn : ¬IsMulCommutative Model) :
    ∃ g : Model, 13 ∣ orderOf g :=
  MatrixModelSelectedProductPrimePeriod.exists_prime_dvd_orderOf 3 64 rows1 rows2 13
    (by decide) (vectors 0) return_thirteen nonreturn_one hn

theorem thirteen_dvd_card (hn : ¬IsMulCommutative Model) : 13 ∣ Nat.card Model :=
  MatrixModelSelectedProductPrimePeriod.prime_dvd_card 3 64 rows1 rows2 13
    (by decide) (vectors 0) return_thirteen nonreturn_one hn

end SymmetricSubgroupAsymptotics.CFSGSuzSelectedProductPrimeThirteen
