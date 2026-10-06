import SymmetricSubgroupAsymptotics.BinaryNormalGeneratorChecks
import SymmetricSubgroupAsymptotics.FiniteCentralizerRowCoordinates
import SymmetricSubgroupAsymptotics.FinitePermutationEncoding
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.FinCases

/-!
# Selected six-pair action 147: Cayley base

This is a resource-bounded split of the selected action-147 certificate.
All finite equations remain kernel checked.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction147ClassPilot

private def generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[8,9,2,3,10,11,0,1,4,5,6,7] : Array (Fin 12))[x.val]!
  invFun x := (#[6,7,2,3,8,9,10,11,0,1,4,5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[7,6,10,11,0,1,2,3,8,9,5,4] : Array (Fin 12))[x.val]!
  invFun x := (#[4,5,6,7,11,10,1,0,8,9,2,3] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def generators (j : Fin 2) : Equiv.Perm (Fin 12) :=
  (if j.val < 1 then generator0 else generator1)

private def codes (i : Fin 60) : Fin (12^12) :=
  (if i.val < 30 then (if i.val < 15 then (if i.val < 7 then (if i.val < 3 then (if i.val < 1 then 73841744394 else (if i.val < 2 then 84944468147 else 100732145525)) else (if i.val < 5 then (if i.val < 4 then 112220896491 else 118436870420) else (if i.val < 6 then 759619139433 else 770918938207))) else (if i.val < 11 then (if i.val < 9 then (if i.val < 8 then 777137607686 else 788238180862) else (if i.val < 10 then 804414017440 else 1672548142111)) else (if i.val < 13 then (if i.val < 12 then 1694982133977 else 1705774562195) else (if i.val < 14 then 1717109900209 else 1728367580357)))) else (if i.val < 22 then (if i.val < 18 then (if i.val < 16 then 2358256633172 else (if i.val < 17 then 2380693837390 else 2391951543564)) else (if i.val < 20 then (if i.val < 19 then 2402743432672 else 2414075536026) else (if i.val < 21 then 3282319828942 else 3293622840068))) else (if i.val < 26 then (if i.val < 24 then (if i.val < 23 then 3315905106481 else 3331611917359) else (if i.val < 25 then 3342715725195 else 3968297511354)) else (if i.val < 28 then (if i.val < 27 then 3979397022755 else 4001413227801) else (if i.val < 29 then 4008098227430 else 4019121187356))))) else (if i.val < 45 then (if i.val < 37 then (if i.val < 33 then (if i.val < 31 then 4896825388587 else (if i.val < 32 then 4903086678622 else 4914607986156)) else (if i.val < 35 then (if i.val < 34 then 4937011040357 else 4952643970857) else (if i.val < 36 then 5573075579632 else 5589327210049))) else (if i.val < 41 then (if i.val < 39 then (if i.val < 38 then 5600120390612 else 5622599474195) else (if i.val < 40 then 5629204168742 else 6506598366851)) else (if i.val < 43 then (if i.val < 42 then 6513093962364 else 6529110850251) else (if i.val < 44 then 6535716596992 else 6557654934655)))) else (if i.val < 52 then (if i.val < 48 then (if i.val < 46 then 7183236735686 else (if i.val < 47 then 7198791044885 else 7205286618090)) else (if i.val < 50 then (if i.val < 49 then 7221303960046 else 7243708111057) else (if i.val < 51 then 8111764594329 else 8123020375888))) else (if i.val < 56 then (if i.val < 54 then (if i.val < 53 then 8138809427617 else 8150220539307) else (if i.val < 55 then 8156359420506 else 8797739599781)) else (if i.val < 58 then (if i.val < 57 then 8808798306319 else 8815059618662) else (if i.val < 59 then 8826314923844 else 8842413667692))))))

private def ranks (i : Fin 60) : ℕ :=
  (if i.val < 30 then (if i.val < 15 then (if i.val < 7 then (if i.val < 3 then (if i.val < 1 then 53 else (if i.val < 2 then 39 else 15)) else (if i.val < 5 then (if i.val < 4 then 6 else 18) else (if i.val < 6 then 50 else 20))) else (if i.val < 11 then (if i.val < 9 then (if i.val < 8 then 25 else 30) else (if i.val < 10 then 3 else 24)) else (if i.val < 13 then (if i.val < 12 then 22 else 48) else (if i.val < 14 then 34 else 33)))) else (if i.val < 22 then (if i.val < 18 then (if i.val < 16 then 5 else (if i.val < 17 then 16 else 40)) else (if i.val < 20 then (if i.val < 19 then 9 else 27) else (if i.val < 21 then 44 else 26))) else (if i.val < 26 then (if i.val < 24 then (if i.val < 23 then 58 else 2) else (if i.val < 25 then 17 else 12)) else (if i.val < 28 then (if i.val < 27 then 32 else 46) else (if i.val < 29 then 49 else 57))))) else (if i.val < 45 then (if i.val < 37 then (if i.val < 33 then (if i.val < 31 then 41 else (if i.val < 32 then 43 else 11)) else (if i.val < 35 then (if i.val < 34 then 52 else 8) else (if i.val < 36 then 19 else 37))) else (if i.val < 41 then (if i.val < 39 then (if i.val < 38 then 1 else 14) else (if i.val < 40 then 59 else 23)) else (if i.val < 43 then (if i.val < 42 then 55 else 10) else (if i.val < 44 then 29 else 51)))) else (if i.val < 52 then (if i.val < 48 then (if i.val < 46 then 35 else (if i.val < 47 then 21 else 45)) else (if i.val < 50 then (if i.val < 49 then 7 else 31) else (if i.val < 51 then 42 else 36))) else (if i.val < 56 then (if i.val < 54 then (if i.val < 53 then 4 else 28) else (if i.val < 55 then 56 else 38)) else (if i.val < 58 then (if i.val < 57 then 47 else 54) else (if i.val < 59 then 13 else 0))))))

private def parents (i : Fin 60) : Fin 60 :=
  (if i.val < 30 then (if i.val < 15 then (if i.val < 7 then (if i.val < 3 then (if i.val < 1 then 51 else (if i.val < 2 then 11 else 48)) else (if i.val < 5 then (if i.val < 4 then 23 else 18) else (if i.val < 6 then 26 else 42))) else (if i.val < 11 then (if i.val < 9 then (if i.val < 8 then 58 else 24) else (if i.val < 10 then 37 else 58)) else (if i.val < 13 then (if i.val < 12 then 32 else 43) else (if i.val < 14 then 35 else 4)))) else (if i.val < 22 then (if i.val < 18 then (if i.val < 16 then 23 else (if i.val < 17 then 34 else 40)) else (if i.val < 20 then (if i.val < 19 then 52 else 2) else (if i.val < 21 then 19 else 38))) else (if i.val < 26 then (if i.val < 24 then (if i.val < 23 then 50 else 59) else (if i.val < 25 then 34 else 15)) else (if i.val < 28 then (if i.val < 27 then 4 else 53) else (if i.val < 29 then 8 else 30))))) else (if i.val < 45 then (if i.val < 37 then (if i.val < 33 then (if i.val < 31 then 40 else (if i.val < 32 then 21 else 15)) else (if i.val < 35 then (if i.val < 34 then 13 else 9) else (if i.val < 36 then 42 else 46))) else (if i.val < 41 then (if i.val < 39 then (if i.val < 38 then 59 else 3) else (if i.val < 40 then 5 else 25)) else (if i.val < 43 then (if i.val < 42 then 55 else 52) else (if i.val < 44 then 16 else 14)))) else (if i.val < 52 then (if i.val < 48 then (if i.val < 46 then 35 else (if i.val < 47 then 32 else 53)) else (if i.val < 50 then (if i.val < 49 then 9 else 24) else (if i.val < 51 then 10 else 6))) else (if i.val < 56 then (if i.val < 54 then (if i.val < 53 then 37 else 2) else (if i.val < 55 then 17 else 11)) else (if i.val < 58 then (if i.val < 57 then 43 else 36) else (if i.val < 59 then 3 else 59))))))

private def letters (i : Fin 60) : Fin 2 :=
  (if i.val < 30 then (if i.val < 15 then (if i.val < 7 then (if i.val < 3 then (if i.val < 1 then 1 else (if i.val < 2 then 1 else 1)) else (if i.val < 5 then (if i.val < 4 then 1 else 0) else (if i.val < 6 then 1 else 1))) else (if i.val < 11 then (if i.val < 9 then (if i.val < 8 then 1 else 0) else (if i.val < 10 then 0 else 0)) else (if i.val < 13 then (if i.val < 12 then 1 else 1) else (if i.val < 14 then 0 else 1)))) else (if i.val < 22 then (if i.val < 18 then (if i.val < 16 then 0 else (if i.val < 17 then 0 else 0)) else (if i.val < 20 then (if i.val < 19 then 0 else 0) else (if i.val < 21 then 0 else 0))) else (if i.val < 26 then (if i.val < 24 then (if i.val < 23 then 0 else 1) else (if i.val < 25 then 1 else 1)) else (if i.val < 28 then (if i.val < 27 then 0 else 1) else (if i.val < 29 then 1 else 0))))) else (if i.val < 45 then (if i.val < 37 then (if i.val < 33 then (if i.val < 31 then 1 else (if i.val < 32 then 1 else 0)) else (if i.val < 35 then (if i.val < 34 then 1 else 1) else (if i.val < 36 then 0 else 1))) else (if i.val < 41 then (if i.val < 39 then (if i.val < 38 then 0 else 1) else (if i.val < 40 then 0 else 1)) else (if i.val < 43 then (if i.val < 42 then 0 else 1) else (if i.val < 44 then 0 else 1)))) else (if i.val < 52 then (if i.val < 48 then (if i.val < 46 then 1 else (if i.val < 47 then 0 else 0)) else (if i.val < 50 then (if i.val < 49 then 0 else 1) else (if i.val < 51 then 1 else 0))) else (if i.val < 56 then (if i.val < 54 then (if i.val < 53 then 1 else 1) else (if i.val < 55 then 0 else 0)) else (if i.val < 58 then (if i.val < 57 then 0 else 0) else (if i.val < 59 then 0 else 0))))))

private def nextRow (i : Fin 60) (j : Fin 2) : Fin 60 :=
  ((if i.val < 30 then (if i.val < 15 then (if i.val < 7 then (if i.val < 3 then (if i.val < 1 then #[42,21] else (if i.val < 2 then #[33,47] else #[19,53])) else (if i.val < 5 then (if i.val < 4 then #[58,38] else #[26,14]) else (if i.val < 6 then #[39,56] else #[51,16]))) else (if i.val < 11 then (if i.val < 9 then (if i.val < 8 then #[23,43] else #[11,28]) else (if i.val < 10 then #[48,34] else #[49,50])) else (if i.val < 13 then (if i.val < 12 then #[55,1] else #[6,22]) else (if i.val < 14 then #[27,33] else #[38,44])))) else (if i.val < 22 then (if i.val < 18 then (if i.val < 16 then #[32,25] else (if i.val < 17 then #[43,37] else #[54,48])) else (if i.val < 20 then (if i.val < 19 then #[4,59] else #[20,9]) else (if i.val < 21 then #[36,10] else #[53,31]))) else (if i.val < 26 then (if i.val < 24 then (if i.val < 23 then #[44,58] else #[15,3]) else (if i.val < 25 then #[8,49] else #[59,40])) else (if i.val < 28 then (if i.val < 27 then #[45,5] else #[0,17]) else (if i.val < 29 then #[34,54] else #[12,39]))))) else (if i.val < 45 then (if i.val < 37 then (if i.val < 33 then (if i.val < 31 then #[29,55] else (if i.val < 32 then #[3,41] else #[46,11])) else (if i.val < 35 then (if i.val < 34 then #[50,8] else #[16,24]) else (if i.val < 36 then #[13,45] else #[57,26]))) else (if i.val < 41 then (if i.val < 39 then (if i.val < 38 then #[9,52] else #[21,18]) else (if i.val < 40 then #[40,4] else #[17,30])) else (if i.val < 43 then (if i.val < 42 then #[24,51] else #[35,6]) else (if i.val < 44 then #[56,12] else #[1,29])))) else (if i.val < 52 then (if i.val < 48 then (if i.val < 46 then #[52,20] else (if i.val < 47 then #[7,36] else #[14,57])) else (if i.val < 50 then (if i.val < 49 then #[25,2] else #[31,19]) else (if i.val < 51 then #[22,35] else #[30,0]))) else (if i.val < 56 then (if i.val < 54 then (if i.val < 53 then #[18,42] else #[47,27]) else (if i.val < 55 then #[5,13] else #[41,15])) else (if i.val < 58 then (if i.val < 57 then #[28,46] else #[2,32]) else (if i.val < 59 then #[10,7] else #[37,23])))))) : Array (Fin 60))[j.val]!

private def prevRow (i : Fin 60) (j : Fin 2) : Fin 60 :=
  ((if i.val < 30 then (if i.val < 15 then (if i.val < 7 then (if i.val < 3 then (if i.val < 1 then #[27,51] else (if i.val < 2 then #[44,11] else #[57,48])) else (if i.val < 5 then (if i.val < 4 then #[31,23] else #[18,39]) else (if i.val < 6 then #[54,26] else #[12,42]))) else (if i.val < 11 then (if i.val < 9 then (if i.val < 8 then #[46,58] else #[24,33]) else (if i.val < 10 then #[37,19] else #[58,20])) else (if i.val < 13 then (if i.val < 12 then #[8,32] else #[29,43]) else (if i.val < 14 then #[35,54] else #[47,4])))) else (if i.val < 22 then (if i.val < 18 then (if i.val < 16 then #[23,55] else (if i.val < 17 then #[34,6] else #[40,27])) else (if i.val < 20 then (if i.val < 19 then #[52,38] else #[2,49]) else (if i.val < 21 then #[19,45] else #[38,0]))) else (if i.val < 26 then (if i.val < 24 then (if i.val < 23 then #[50,12] else #[7,59]) else (if i.val < 25 then #[41,34] else #[48,15])) else (if i.val < 28 then (if i.val < 27 then #[4,36] else #[13,53]) else (if i.val < 29 then #[56,8] else #[30,44]))))) else (if i.val < 45 then (if i.val < 37 then (if i.val < 33 then (if i.val < 31 then #[51,40] else (if i.val < 32 then #[49,21] else #[15,57])) else (if i.val < 35 then (if i.val < 34 then #[1,13] else #[28,9]) else (if i.val < 36 then #[42,50] else #[20,46]))) else (if i.val < 41 then (if i.val < 39 then (if i.val < 38 then #[59,16] else #[14,3]) else (if i.val < 40 then #[5,29] else #[39,25])) else (if i.val < 43 then (if i.val < 42 then #[55,31] else #[0,52]) else (if i.val < 44 then #[16,7] else #[22,14])))) else (if i.val < 52 then (if i.val < 48 then (if i.val < 46 then #[26,35] else (if i.val < 47 then #[32,56] else #[53,1])) else (if i.val < 50 then (if i.val < 49 then #[9,17] else #[10,24]) else (if i.val < 51 then #[33,10] else #[6,41]))) else (if i.val < 56 then (if i.val < 54 then (if i.val < 53 then #[45,37] else #[21,2]) else (if i.val < 55 then #[17,28] else #[11,30])) else (if i.val < 58 then (if i.val < 57 then #[43,5] else #[36,47]) else (if i.val < 59 then #[3,22] else #[25,18])))))) : Array (Fin 60))[j.val]!

private theorem parent_lt_checked : ∀ i : Fin 60,
    i ≠ 59 → ranks (parents i) < ranks i := (Fin.addCases (m := 30) (n := 30) (Fin.addCases (m := 15) (n := 15) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 15) (n := 15) (by decide +kernel) (by decide +kernel)))

private theorem parent_next_checked : ∀ i : Fin 60,
    i ≠ 59 → nextRow (parents i) (letters i) = i := (Fin.addCases (m := 30) (n := 30) (Fin.addCases (m := 15) (n := 15) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 15) (n := 15) (by decide +kernel) (by decide +kernel)))

def certificate : EncodedCayleyCertificate
    (permutationGeneratorEncoding generators) 60 where
  rows := codes
  identity := 59
  identity_eq := by decide +kernel
  next := nextRow
  next_eq := (Fin.addCases (m := 30) (n := 30) (Fin.addCases (m := 15) (n := 15) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 15) (n := 15) (by decide +kernel) (by decide +kernel)))
  rank := ranks
  parent i _ := parents i
  letter i _ := letters i
  parent_lt := parent_lt_checked
  parent_next := parent_next_checked

private theorem codes_strict : StrictMono codes :=
  Fin.strictMono_iff_lt_succ.mpr (Fin.addCases (m := 29) (n := 30) (Fin.addCases (m := 14) (n := 15) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 15) (n := 15) (by decide +kernel) (by decide +kernel)))

theorem rows_injective : Function.Injective certificate.rows :=
  codes_strict.injective

theorem exact_card :
    Nat.card (Subgroup.closure (Set.range generators)) = 60 :=
  certificate.card_closure rows_injective

private theorem prev_checked : ∀ i j,
    certificate.next (prevRow i j) j = i := (Fin.addCases (m := 30) (n := 30) (Fin.addCases (m := 15) (n := 15) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 15) (n := 15) (by decide +kernel) (by decide +kernel)))

@[reducible] def group : Group (FiniteGroupRow 60) :=
  certificate.rowGroup rows_injective prevRow prev_checked

def originalEquiv : letI := group
    FiniteGroupRow 60 ≃* Subgroup.closure (Set.range generators) :=
  certificate.rowEquiv rows_injective prevRow prev_checked

abbrev Source := FiniteGroupRow 60

instance selectedSourceGroup : Group Source := group

def ambient (j : Fin 2) : Source :=
  ⟨certificate.next certificate.identity j⟩

theorem ambient_full : Subgroup.closure (Set.range ambient) = ⊤ :=
  certificate.row_generators_full rows_injective prevRow prev_checked

theorem source_card : Nat.card Source = 60 := by
  rw [Nat.card_eq_fintype_card]
  rfl
end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction147ClassPilot

end
