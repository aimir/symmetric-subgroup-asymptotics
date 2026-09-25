import SymmetricSubgroupAsymptotics.FiniteCayleyGroup
import SymmetricSubgroupAsymptotics.FinitePermutationEncoding
import Mathlib.Order.Fin.Basic

/-!
# Compact literal action certificate 8T11

Generated from the original menu permutations by export_lean_menu_cayley.py.
All finite equations use Lean's kernel. BFS parents establish actual group
membership; numeric permutation codes establish faithfulness. This certifies
this original action, not finite-menu or normal-registry completeness.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryMenuCayley8T11

private def generator0 : Equiv.Perm (Fin 8) where
  toFun x := (#[4,1,6,3,0,5,2,7] : Array (Fin 8))[x.val]!
  invFun x := (#[4,1,6,3,0,5,2,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def generator1 : Equiv.Perm (Fin 8) where
  toFun x := (#[2,3,4,5,6,7,0,1] : Array (Fin 8))[x.val]!
  invFun x := (#[6,7,0,1,2,3,4,5] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def generator2 : Equiv.Perm (Fin 8) where
  toFun x := (#[3,2,5,4,7,6,1,0] : Array (Fin 8))[x.val]!
  invFun x := (#[7,6,1,0,3,2,5,4] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def generators (j : Fin 3) : Equiv.Perm (Fin 8) :=
  (if j.val < 1 then generator0 else (if j.val < 2 then generator1 else generator2))

private def codes (i : Fin 16) : Fin (8^8) :=
  (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 489811 else 1521751) else (if i.val < 3 then 2353946 else 3385886)) else (if i.val < 6 then (if i.val < 5 then 4988389 else 6053089) else (if i.val < 7 then 6852524 else 7917224))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 8745331 else 9777271) else (if i.val < 11 then 10609466 else 11641406)) else (if i.val < 14 then (if i.val < 13 then 13505989 else 14570689) else (if i.val < 15 then 15370124 else 16434824))))
private def ranks (i : Fin 16) : ℕ :=
  (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 3 else 8) else (if i.val < 3 then 2 else 4)) else (if i.val < 6 then (if i.val < 5 then 7 else 13) else (if i.val < 7 then 6 else 9))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 5 else 11) else (if i.val < 11 then 14 else 12)) else (if i.val < 14 then (if i.val < 13 then 10 else 15) else (if i.val < 15 then 1 else 0))))
private def parents (i : Fin 16) : Fin 16 :=
  (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 15 else 0) else (if i.val < 3 then 15 else 14)) else (if i.val < 6 then (if i.val < 5 then 2 else 4) else (if i.val < 7 then 2 else 3))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 14 else 8) else (if i.val < 11 then 7 else 6)) else (if i.val < 14 then (if i.val < 13 then 3 else 12) else (if i.val < 15 then 15 else 15))))
private def letters (i : Fin 16) : Fin 3 :=
  (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 2 else 0) else (if i.val < 3 then 1 else 1)) else (if i.val < 6 then (if i.val < 5 then 2 else 0) else (if i.val < 7 then 1 else 1))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 2 else 0) else (if i.val < 11 then 1 else 1)) else (if i.val < 14 then (if i.val < 13 then 2 else 0) else (if i.val < 15 then 0 else 0))))
private def nextRow (i : Fin 16) (j : Fin 3) : Fin 16 :=
  ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,4,6] else #[0,5,14]) else (if i.val < 3 then #[3,6,4] else #[2,7,12])) else (if i.val < 6 then (if i.val < 5 then #[5,9,11] else #[4,8,3]) else (if i.val < 7 then #[7,11,9] else #[6,10,1]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[9,12,7] else #[8,13,15]) else (if i.val < 11 then #[11,14,5] else #[10,15,13])) else (if i.val < 14 then (if i.val < 13 then #[13,1,10] else #[12,0,2]) else (if i.val < 15 then #[15,3,8] else #[14,2,0])))) : Array (Fin 16))[j.val]!
private def prevRow (i : Fin 16) (j : Fin 3) : Fin 16 :=
  ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,13,15] else #[0,12,7]) else (if i.val < 3 then #[3,15,13] else #[2,14,5])) else (if i.val < 6 then (if i.val < 5 then #[5,0,2] else #[4,1,10]) else (if i.val < 7 then #[7,2,0] else #[6,3,8]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[9,5,14] else #[8,4,6]) else (if i.val < 11 then #[11,7,12] else #[10,6,4])) else (if i.val < 14 then (if i.val < 13 then #[13,8,3] else #[12,9,11]) else (if i.val < 15 then #[15,10,1] else #[14,11,9])))) : Array (Fin 16))[j.val]!

private theorem parent_lt_checked : ∀ i : Fin 16,
    i ≠ 15 → ranks (parents i) < ranks i := (by decide +kernel)
private theorem parent_next_checked : ∀ i : Fin 16,
    i ≠ 15 → nextRow (parents i) (letters i) = i := (by decide +kernel)

def certificate : EncodedCayleyCertificate
    (permutationGeneratorEncoding generators) 16 where
  rows := codes
  identity := 15
  identity_eq := by decide +kernel
  next := nextRow
  next_eq := (by decide +kernel)
  rank := ranks
  parent i _ := parents i
  letter i _ := letters i
  parent_lt := parent_lt_checked
  parent_next := parent_next_checked

private theorem codes_strict : StrictMono codes :=
  Fin.strictMono_iff_lt_succ.mpr (by decide +kernel)

theorem rows_injective : Function.Injective certificate.rows := codes_strict.injective

theorem exact_card : Nat.card (Subgroup.closure (Set.range generators)) = 16 :=
  certificate.card_closure rows_injective

private theorem prev_checked : ∀ i j, certificate.next (prevRow i j) j = i :=
  (by decide +kernel)

/-- Executable multiplication and inverse, with laws proved by faithfulness. -/
@[reducible] def group : Group (FiniteGroupRow 16) :=
  certificate.rowGroup rows_injective prevRow prev_checked

/-- Exact identification with the original literal permutation subgroup. -/
def originalEquiv : letI := group
    FiniteGroupRow 16 ≃* Subgroup.closure (Set.range generators) :=
  certificate.rowEquiv rows_injective prevRow prev_checked

end SymmetricSubgroupAsymptotics.BinaryMenuCayley8T11
