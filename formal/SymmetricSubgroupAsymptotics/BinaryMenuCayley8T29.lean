import SymmetricSubgroupAsymptotics.FiniteCayleyGroup
import SymmetricSubgroupAsymptotics.FinitePermutationEncoding
import Mathlib.Order.Fin.Basic

/-!
# Compact literal action certificate 8T29

Generated from the original menu permutations by export_lean_menu_cayley.py.
All finite equations use Lean's kernel. BFS parents establish actual group
membership; numeric permutation codes establish faithfulness. This certifies
this original action, not finite-menu or normal-registry completeness.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryMenuCayley8T29

private def generator0 : Equiv.Perm (Fin 8) where
  toFun x := (#[7,2,1,4,3,6,5,0] : Array (Fin 8))[x.val]!
  invFun x := (#[7,2,1,4,3,6,5,0] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def generator1 : Equiv.Perm (Fin 8) where
  toFun x := (#[2,7,0,5,6,3,4,1] : Array (Fin 8))[x.val]!
  invFun x := (#[2,7,0,5,6,3,4,1] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def generator2 : Equiv.Perm (Fin 8) where
  toFun x := (#[4,5,6,7,0,1,2,3] : Array (Fin 8))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def generator3 : Equiv.Perm (Fin 8) where
  toFun x := (#[2,1,0,4,5,6,3,7] : Array (Fin 8))[x.val]!
  invFun x := (#[2,1,0,6,3,4,5,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def generator4 : Equiv.Perm (Fin 8) where
  toFun x := (#[2,1,0,3,6,5,4,7] : Array (Fin 8))[x.val]!
  invFun x := (#[2,1,0,3,6,5,4,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def generators (j : Fin 5) : Equiv.Perm (Fin 8) :=
  (if j.val < 2 then (if j.val < 1 then generator0 else generator1) else (if j.val < 3 then generator2 else (if j.val < 4 then generator3 else generator4)))

private def codes (i : Fin 64) : Fin (8^8) :=
  (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 941143 else 1006033) else (if i.val < 3 then 1174103 else 1238993)) else (if i.val < 6 then (if i.val < 5 then 1457617 else 1521751) else (if i.val < 7 then 1690577 else 1754711))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 3038266 else 3102904) else (if i.val < 11 then 3271226 else 3335864)) else (if i.val < 14 then (if i.val < 13 then 3554488 else 3618874) else (if i.val < 15 then 3787448 else 3851834)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 5135809 else 5199943) else (if i.val < 19 then 5368769 else 5432903)) else (if i.val < 22 then (if i.val < 21 then 5651527 else 5716417) else (if i.val < 23 then 5884487 else 5949377))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 6336302 else 6529964) else (if i.val < 27 then 6583598 else 6648236)) else (if i.val < 30 then (if i.val < 29 then 6852524 else 7045934) else (if i.val < 31 then 8132012 else 8196398))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 8433397 else 8627059) else (if i.val < 35 then 8680693 else 8745331)) else (if i.val < 38 then (if i.val < 37 then 8949619 else 9143029) else (if i.val < 39 then 10229107 else 10293493))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 10530716 else 10724126) else (if i.val < 43 then 10778012 else 10842398)) else (if i.val < 46 then (if i.val < 45 then 11046686 else 11240348) else (if i.val < 47 then 12326174 else 12390812)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 12627811 else 12821221) else (if i.val < 51 then 12875107 else 12939493)) else (if i.val < 54 then (if i.val < 53 then 13143781 else 13337443) else (if i.val < 55 then 14423269 else 14487907))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 15621256 else 15685642) else (if i.val < 59 then 15854216 else 15918602)) else (if i.val < 62 then (if i.val < 61 then 16137226 else 16201864) else (if i.val < 63 then 16370186 else 16434824))))))
private def ranks (i : Fin 64) : ℕ :=
  (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 23 else 9) else (if i.val < 3 then 25 else 8)) else (if i.val < 6 then (if i.val < 5 then 48 else 1) else (if i.val < 7 then 47 else 24))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 30 else 52) else (if i.val < 11 then 2 else 53)) else (if i.val < 14 then (if i.val < 13 then 11 else 31) else (if i.val < 15 then 12 else 29)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 6 else 57) else (if i.val < 19 then 37 else 56)) else (if i.val < 22 then (if i.val < 21 then 19 else 36) else (if i.val < 23 then 15 else 43))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 14 else 32) else (if i.val < 27 then 54 else 33)) else (if i.val < 30 then (if i.val < 29 then 3 else 55) else (if i.val < 31 then 35 else 13))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 16 else 45) else (if i.val < 35 then 59 else 7)) else (if i.val < 38 then (if i.val < 37 then 39 else 58) else (if i.val < 39 then 38 else 22))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 61 else 10) else (if i.val < 43 then 26 else 49)) else (if i.val < 46 then (if i.val < 45 then 40 else 27) else (if i.val < 47 then 50 else 60)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 62 else 51) else (if i.val < 51 then 34 else 46)) else (if i.val < 54 then (if i.val < 53 then 44 else 28) else (if i.val < 55 then 21 else 63))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 20 else 4) else (if i.val < 59 then 17 else 5)) else (if i.val < 62 then (if i.val < 61 then 41 else 18) else (if i.val < 63 then 42 else 0))))))
private def parents (i : Fin 64) : Fin 64 :=
  (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 3 else 5) else (if i.val < 3 then 1 else 5)) else (if i.val < 6 then (if i.val < 5 then 0 else 63) else (if i.val < 7 then 0 else 3))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 12 else 15) else (if i.val < 11 then 63 else 15)) else (if i.val < 14 then (if i.val < 13 then 10 else 14) else (if i.val < 15 then 10 else 12)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 5 else 21) else (if i.val < 19 then 22 else 21)) else (if i.val < 22 then (if i.val < 21 then 59 else 22) else (if i.val < 23 then 57 else 20))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 28 else 31) else (if i.val < 27 then 25 else 31)) else (if i.val < 30 then (if i.val < 29 then 63 else 25) else (if i.val < 31 then 24 else 28))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 57 else 39) else (if i.val < 35 then 38 else 5)) else (if i.val < 38 then (if i.val < 37 then 32 else 38) else (if i.val < 39 then 32 else 35))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 44 else 10) else (if i.val < 43 then 41 else 2)) else (if i.val < 46 then (if i.val < 45 then 58 else 41) else (if i.val < 47 then 42 else 44)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 60 else 53) else (if i.val < 51 then 24 else 0)) else (if i.val < 54 then (if i.val < 53 then 56 else 12) else (if i.val < 55 then 16 else 52))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 59 else 63) else (if i.val < 59 then 57 else 63)) else (if i.val < 62 then (if i.val < 61 then 58 else 57) else (if i.val < 63 then 58 else 63))))))
private def letters (i : Fin 64) : Fin 5 :=
  (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 3 else 4) else (if i.val < 3 then 3 else 3)) else (if i.val < 6 then (if i.val < 5 then 4 else 0) else (if i.val < 7 then 3 else 4))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 4 else 3) else (if i.val < 11 then 1 else 4)) else (if i.val < 14 then (if i.val < 13 then 3 else 3) else (if i.val < 15 then 4 else 3)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 1 else 4) else (if i.val < 19 then 4 else 3)) else (if i.val < 22 then (if i.val < 21 then 0 else 3) else (if i.val < 23 then 0 else 3))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 4 else 3) else (if i.val < 27 then 3 else 4)) else (if i.val < 30 then (if i.val < 29 then 2 else 4) else (if i.val < 31 then 3 else 3))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 2 else 3) else (if i.val < 35 then 4 else 2)) else (if i.val < 38 then (if i.val < 37 then 4 else 3) else (if i.val < 39 then 3 else 4))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 4 else 2) else (if i.val < 43 then 3 else 2)) else (if i.val < 46 then (if i.val < 45 then 2 else 4) else (if i.val < 47 then 4 else 3)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 2 else 4) else (if i.val < 51 then 0 else 2)) else (if i.val < 54 then (if i.val < 53 then 2 else 2) else (if i.val < 55 then 2 else 3))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 3 else 3) else (if i.val < 59 then 3 else 4)) else (if i.val < 62 then (if i.val < 61 then 3 else 4) else (if i.val < 63 then 4 else 0))))))
private def nextRow (i : Fin 64) (j : Fin 5) : Fin 64 :=
  ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[58,21,51,6,4] else #[14,20,39,2,5]) else (if i.val < 3 then #[56,23,43,4,6] else #[12,22,31,0,7])) else (if i.val < 6 then (if i.val < 5 then #[11,17,55,7,0] else #[63,16,35,3,1]) else (if i.val < 7 then #[9,19,47,5,2] else #[61,18,27,1,3]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[18,61,49,14,12] else #[6,60,37,10,13]) else (if i.val < 11 then #[16,63,41,12,14] else #[4,62,29,8,15])) else (if i.val < 14 then (if i.val < 13 then #[3,57,53,15,8] else #[23,56,33,11,9]) else (if i.val < 15 then #[1,59,45,13,10] else #[21,58,25,9,11])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[10,5,54,22,20] else #[62,4,34,18,21]) else (if i.val < 19 then #[8,7,46,20,22] else #[60,6,26,16,23])) else (if i.val < 22 then (if i.val < 21 then #[59,1,50,23,16] else #[15,0,38,19,17]) else (if i.val < 23 then #[57,3,42,21,18] else #[13,2,30,17,19]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[50,45,59,30,28] else #[38,44,15,26,29]) else (if i.val < 27 then #[48,47,19,28,30] else #[36,46,7,24,31])) else (if i.val < 30 then (if i.val < 29 then #[35,41,63,31,24] else #[55,40,11,27,25]) else (if i.val < 31 then #[33,43,23,29,26] else #[53,42,3,25,27]))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then #[42,53,57,38,36] else #[30,52,13,34,37]) else (if i.val < 35 then #[40,55,17,36,38] else #[28,54,5,32,39])) else (if i.val < 38 then (if i.val < 37 then #[27,49,61,39,32] else #[47,48,9,35,33]) else (if i.val < 39 then #[25,51,21,37,34] else #[45,50,1,33,35]))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then #[34,29,62,46,44] else #[54,28,10,42,45]) else (if i.val < 43 then #[32,31,22,44,46] else #[52,30,2,40,47])) else (if i.val < 46 then (if i.val < 45 then #[51,25,58,47,40] else #[39,24,14,43,41]) else (if i.val < 47 then #[49,27,18,45,42] else #[37,26,6,41,43])))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then #[26,37,60,54,52] else #[46,36,8,50,53]) else (if i.val < 51 then #[24,39,20,52,54] else #[44,38,0,48,55])) else (if i.val < 54 then (if i.val < 53 then #[43,33,56,55,48] else #[31,32,12,51,49]) else (if i.val < 55 then #[41,35,16,53,50] else #[29,34,4,49,51]))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then #[2,13,52,62,60] else #[22,12,32,58,61]) else (if i.val < 59 then #[0,15,44,60,62] else #[20,14,24,56,63])) else (if i.val < 62 then (if i.val < 61 then #[19,9,48,63,56] else #[7,8,36,59,57]) else (if i.val < 63 then #[17,11,40,61,58] else #[5,10,28,57,59])))))) : Array (Fin 64))[j.val]!
private def prevRow (i : Fin 64) (j : Fin 5) : Fin 64 :=
  ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[58,21,51,3,4] else #[14,20,39,7,5]) else (if i.val < 3 then #[56,23,43,1,6] else #[12,22,31,5,7])) else (if i.val < 6 then (if i.val < 5 then #[11,17,55,2,0] else #[63,16,35,6,1]) else (if i.val < 7 then #[9,19,47,0,2] else #[61,18,27,4,3]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[18,61,49,11,12] else #[6,60,37,15,13]) else (if i.val < 11 then #[16,63,41,9,14] else #[4,62,29,13,15])) else (if i.val < 14 then (if i.val < 13 then #[3,57,53,10,8] else #[23,56,33,14,9]) else (if i.val < 15 then #[1,59,45,8,10] else #[21,58,25,12,11])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[10,5,54,19,20] else #[62,4,34,23,21]) else (if i.val < 19 then #[8,7,46,17,22] else #[60,6,26,21,23])) else (if i.val < 22 then (if i.val < 21 then #[59,1,50,18,16] else #[15,0,38,22,17]) else (if i.val < 23 then #[57,3,42,16,18] else #[13,2,30,20,19]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[50,45,59,27,28] else #[38,44,15,31,29]) else (if i.val < 27 then #[48,47,19,25,30] else #[36,46,7,29,31])) else (if i.val < 30 then (if i.val < 29 then #[35,41,63,26,24] else #[55,40,11,30,25]) else (if i.val < 31 then #[33,43,23,24,26] else #[53,42,3,28,27]))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then #[42,53,57,35,36] else #[30,52,13,39,37]) else (if i.val < 35 then #[40,55,17,33,38] else #[28,54,5,37,39])) else (if i.val < 38 then (if i.val < 37 then #[27,49,61,34,32] else #[47,48,9,38,33]) else (if i.val < 39 then #[25,51,21,32,34] else #[45,50,1,36,35]))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then #[34,29,62,43,44] else #[54,28,10,47,45]) else (if i.val < 43 then #[32,31,22,41,46] else #[52,30,2,45,47])) else (if i.val < 46 then (if i.val < 45 then #[51,25,58,42,40] else #[39,24,14,46,41]) else (if i.val < 47 then #[49,27,18,40,42] else #[37,26,6,44,43])))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then #[26,37,60,51,52] else #[46,36,8,55,53]) else (if i.val < 51 then #[24,39,20,49,54] else #[44,38,0,53,55])) else (if i.val < 54 then (if i.val < 53 then #[43,33,56,50,48] else #[31,32,12,54,49]) else (if i.val < 55 then #[41,35,16,48,50] else #[29,34,4,52,51]))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then #[2,13,52,59,60] else #[22,12,32,63,61]) else (if i.val < 59 then #[0,15,44,57,62] else #[20,14,24,61,63])) else (if i.val < 62 then (if i.val < 61 then #[19,9,48,58,56] else #[7,8,36,62,57]) else (if i.val < 63 then #[17,11,40,56,58] else #[5,10,28,60,59])))))) : Array (Fin 64))[j.val]!

private theorem parent_lt_checked : ∀ i : Fin 64,
    i ≠ 63 → ranks (parents i) < ranks i := (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))
private theorem parent_next_checked : ∀ i : Fin 64,
    i ≠ 63 → nextRow (parents i) (letters i) = i := (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))

def certificate : EncodedCayleyCertificate
    (permutationGeneratorEncoding generators) 64 where
  rows := codes
  identity := 63
  identity_eq := by decide +kernel
  next := nextRow
  next_eq := (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))
  rank := ranks
  parent i _ := parents i
  letter i _ := letters i
  parent_lt := parent_lt_checked
  parent_next := parent_next_checked

private theorem codes_strict : StrictMono codes :=
  Fin.strictMono_iff_lt_succ.mpr (Fin.addCases (m := 31) (n := 32) (Fin.addCases (m := 15) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))

theorem rows_injective : Function.Injective certificate.rows := codes_strict.injective

theorem exact_card : Nat.card (Subgroup.closure (Set.range generators)) = 64 :=
  certificate.card_closure rows_injective

private theorem prev_checked : ∀ i j, certificate.next (prevRow i j) j = i :=
  (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))

/-- Executable multiplication and inverse, with laws proved by faithfulness. -/
@[reducible] def group : Group (FiniteGroupRow 64) :=
  certificate.rowGroup rows_injective prevRow prev_checked

/-- Exact identification with the original literal permutation subgroup. -/
def originalEquiv : letI := group
    FiniteGroupRow 64 ≃* Subgroup.closure (Set.range generators) :=
  certificate.rowEquiv rows_injective prevRow prev_checked

end SymmetricSubgroupAsymptotics.BinaryMenuCayley8T29
