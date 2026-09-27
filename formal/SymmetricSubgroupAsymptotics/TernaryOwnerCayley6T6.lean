import SymmetricSubgroupAsymptotics.FiniteCayleyGroup
import SymmetricSubgroupAsymptotics.FinitePermutationEncoding
import Mathlib.Order.Fin.Basic

/-!
# Literal c=1 high action certificate 6T6

Generated from certificates/data/primitive_rank.jsonl.gz by export_lean_c1_degree_six.py.
Selected transitive row 20; raw-line SHA256 29e45bfd19a6a4be6024d413bdca5d2e25e91e9d2642275bfe6d495d8c4b7bbd.
All finite equations use Lean's kernel. BFS parents establish actual group
membership; numeric permutation codes establish faithfulness. This proves the literal selected action only;
high-pair coverage and earlier-owner acceptance remain separate theorems.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section

namespace SymmetricSubgroupAsymptotics.TernaryOwnerCayley6T6

private def generator0 : Equiv.Perm (Fin 6) where
  toFun x := (#[0,1,5,3,4,2] : Array (Fin 6))[x.val]!
  invFun x := (#[0,1,5,3,4,2] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def generator1 : Equiv.Perm (Fin 6) where
  toFun x := (#[2,3,4,5,0,1] : Array (Fin 6))[x.val]!
  invFun x := (#[4,5,0,1,2,3] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def generators (j : Fin 2) : Equiv.Perm (Fin 6) :=
  (if j.val < 1 then generator0 else generator1)

private def codes (i : Fin 24) : Fin (6^6) :=
  (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then 2950 else (if i.val < 2 then 3595 else 6820)) else (if i.val < 4 then 7465 else (if i.val < 5 then 8375 else 9020))) else (if i.val < 9 then (if i.val < 7 then 12245 else (if i.val < 8 then 12890 else 17055)) else (if i.val < 10 then 17700 else (if i.val < 11 then 20925 else 21570)))) else (if i.val < 18 then (if i.val < 15 then (if i.val < 13 then 26170 else (if i.val < 14 then 26815 else 30040)) else (if i.val < 16 then 30685 else (if i.val < 17 then 31595 else 32240))) else (if i.val < 21 then (if i.val < 19 then 35465 else (if i.val < 20 then 36110 else 40275)) else (if i.val < 22 then 40920 else (if i.val < 23 then 44145 else 44790)))))
private def ranks (i : Fin 24) : ℕ :=
  (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then 9 else (if i.val < 2 then 12 else 11)) else (if i.val < 4 then 15 else (if i.val < 5 then 3 else 2))) else (if i.val < 9 then (if i.val < 7 then 21 else (if i.val < 8 then 19 else 20)) else (if i.val < 10 then 16 else (if i.val < 11 then 17 else 1)))) else (if i.val < 18 then (if i.val < 15 then (if i.val < 13 then 5 else (if i.val < 14 then 8 else 7)) else (if i.val < 16 then 10 else (if i.val < 17 then 6 else 4))) else (if i.val < 21 then (if i.val < 19 then 23 else (if i.val < 20 then 22 else 18)) else (if i.val < 22 then 13 else (if i.val < 23 then 14 else 0)))))
private def parents (i : Fin 24) : Fin 24 :=
  (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then 12 else (if i.val < 2 then 13 else 14)) else (if i.val < 4 then 15 else (if i.val < 5 then 11 else 23))) else (if i.val < 9 then (if i.val < 7 then 10 else (if i.val < 8 then 22 else 3)) else (if i.val < 10 then 15 else (if i.val < 11 then 2 else 23)))) else (if i.val < 18 then (if i.val < 15 then (if i.val < 13 then 5 else (if i.val < 14 then 17 else 4)) else (if i.val < 16 then 16 else (if i.val < 17 then 4 else 5))) else (if i.val < 21 then (if i.val < 19 then 8 else (if i.val < 20 then 20 else 1)) else (if i.val < 22 then 13 else (if i.val < 23 then 0 else 23)))))
private def letters (i : Fin 24) : Fin 2 :=
  (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then 0 else (if i.val < 2 then 0 else 0)) else (if i.val < 4 then 0 else (if i.val < 5 then 1 else 1))) else (if i.val < 9 then (if i.val < 7 then 1 else (if i.val < 8 then 1 else 1)) else (if i.val < 10 then 1 else (if i.val < 11 then 1 else 0)))) else (if i.val < 18 then (if i.val < 15 then (if i.val < 13 then 1 else (if i.val < 14 then 1 else 1)) else (if i.val < 16 then 1 else (if i.val < 17 then 0 else 0))) else (if i.val < 21 then (if i.val < 19 then 1 else (if i.val < 20 then 1 else 1)) else (if i.val < 22 then 1 else (if i.val < 23 then 1 else 0)))))
private def nextRow (i : Fin 24) (j : Fin 2) : Fin 24 :=
  ((if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then #[12,22] else (if i.val < 2 then #[13,20] else #[14,10])) else (if i.val < 4 then #[15,8] else (if i.val < 5 then #[16,14] else #[17,12]))) else (if i.val < 9 then (if i.val < 7 then #[18,2] else (if i.val < 8 then #[19,0] else #[20,18])) else (if i.val < 10 then #[21,16] else (if i.val < 11 then #[22,6] else #[23,4])))) else (if i.val < 18 then (if i.val < 15 then (if i.val < 13 then #[0,23] else (if i.val < 14 then #[1,21] else #[2,11])) else (if i.val < 16 then #[3,9] else (if i.val < 17 then #[4,15] else #[5,13]))) else (if i.val < 21 then (if i.val < 19 then #[6,3] else (if i.val < 20 then #[7,1] else #[8,19])) else (if i.val < 22 then #[9,17] else (if i.val < 23 then #[10,7] else #[11,5]))))) : Array (Fin 24))[j.val]!
private def prevRow (i : Fin 24) (j : Fin 2) : Fin 24 :=
  ((if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then #[12,7] else (if i.val < 2 then #[13,19] else #[14,6])) else (if i.val < 4 then #[15,18] else (if i.val < 5 then #[16,11] else #[17,23]))) else (if i.val < 9 then (if i.val < 7 then #[18,10] else (if i.val < 8 then #[19,22] else #[20,3])) else (if i.val < 10 then #[21,15] else (if i.val < 11 then #[22,2] else #[23,14])))) else (if i.val < 18 then (if i.val < 15 then (if i.val < 13 then #[0,5] else (if i.val < 14 then #[1,17] else #[2,4])) else (if i.val < 16 then #[3,16] else (if i.val < 17 then #[4,9] else #[5,21]))) else (if i.val < 21 then (if i.val < 19 then #[6,8] else (if i.val < 20 then #[7,20] else #[8,1])) else (if i.val < 22 then #[9,13] else (if i.val < 23 then #[10,0] else #[11,12]))))) : Array (Fin 24))[j.val]!

private theorem parent_lt_checked : ∀ i : Fin 24,
    i ≠ 23 → ranks (parents i) < ranks i := (Fin.addCases (m := 12) (n := 12) (by decide +kernel) (by decide +kernel))
private theorem parent_next_checked : ∀ i : Fin 24,
    i ≠ 23 → nextRow (parents i) (letters i) = i := (Fin.addCases (m := 12) (n := 12) (by decide +kernel) (by decide +kernel))

def certificate : EncodedCayleyCertificate
    (permutationGeneratorEncoding generators) 24 where
  rows := codes
  identity := 23
  identity_eq := by decide +kernel
  next := nextRow
  next_eq := (Fin.addCases (m := 12) (n := 12) (by decide +kernel) (by decide +kernel))
  rank := ranks
  parent i _ := parents i
  letter i _ := letters i
  parent_lt := parent_lt_checked
  parent_next := parent_next_checked

private theorem codes_strict : StrictMono codes :=
  Fin.strictMono_iff_lt_succ.mpr (Fin.addCases (m := 11) (n := 12) (by decide +kernel) (by decide +kernel))

theorem rows_injective : Function.Injective certificate.rows := codes_strict.injective

theorem exact_card : Nat.card (Subgroup.closure (Set.range generators)) = 24 :=
  certificate.card_closure rows_injective

private theorem prev_checked : ∀ i j, certificate.next (prevRow i j) j = i :=
  (Fin.addCases (m := 12) (n := 12) (by decide +kernel) (by decide +kernel))

/-- Executable multiplication and inverse, with laws proved by faithfulness. -/
@[reducible] def group : Group (FiniteGroupRow 24) :=
  certificate.rowGroup rows_injective prevRow prev_checked

/-- Exact identification with the original literal permutation subgroup. -/
def originalEquiv : letI := group
    FiniteGroupRow 24 ≃* Subgroup.closure (Set.range generators) :=
  certificate.rowEquiv rows_injective prevRow prev_checked

/-- Exact one-based image lists bind the selected original source tuple. -/
theorem sourceGenerator_images : ∀ j : Fin 2, ∀ x : Fin 6,
    (generators j x).val + 1 =
      ((#[#[1,2,6,4,5,3],#[3,4,5,6,1,2]] : Array (Array ℕ))[j.val]!)[x.val]! := by
  decide +kernel

end SymmetricSubgroupAsymptotics.TernaryOwnerCayley6T6
