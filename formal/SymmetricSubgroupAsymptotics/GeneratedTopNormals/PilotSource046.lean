import SymmetricSubgroupAsymptotics.FiniteCayleyGroup
import SymmetricSubgroupAsymptotics.FinitePermutationEncoding
import Mathlib.Order.Fin.Basic

/-!
# Compact literal action certificate Top046

Generated from actual projected menu permutations by export_lean_top_registry.py.
All finite equations use Lean's kernel. BFS parents establish actual group
membership; numeric permutation codes establish faithfulness. This certifies
this original action, not finite-menu or normal-registry completeness.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryTopSource046

private def generator0 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,1,2,3,5,4,7,6] : Array (Fin 8))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def generator1 : Equiv.Perm (Fin 8) where
  toFun x := (#[1,0,3,2,6,7,4,5] : Array (Fin 8))[x.val]!
  invFun x := (#[1,0,3,2,6,7,4,5] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def generator2 : Equiv.Perm (Fin 8) where
  toFun x := (#[6,5,4,7,1,2,3,0] : Array (Fin 8))[x.val]!
  invFun x := (#[7,4,5,6,2,1,0,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def generators (j : Fin 3) : Equiv.Perm (Fin 8) :=
  (if j.val < 1 then generator0 else (if j.val < 2 then generator1 else generator2))

private def codes (i : Fin 16) : Fin (8^8) :=
  (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 859495 else 859950) else (if i.val < 3 then 2722293 else 2722748)) else (if i.val < 6 then (if i.val < 5 then 4471285 else 4471740) else (if i.val < 7 then 6335847 else 6336302))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 9925146 else 9925825) else (if i.val < 11 then 11788826 else 11789505)) else (if i.val < 14 then (if i.val < 13 then 14569555 else 14571144) else (if i.val < 15 then 16433235 else 16434824))))
private def ranks (i : Fin 16) : ℕ :=
  (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 5 else 3) else (if i.val < 3 then 10 else 6)) else (if i.val < 6 then (if i.val < 5 then 8 else 12) else (if i.val < 7 then 11 else 7))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 14 else 4) else (if i.val < 11 then 15 else 2)) else (if i.val < 14 then (if i.val < 13 then 9 else 1) else (if i.val < 15 then 13 else 0))))
private def parents (i : Fin 16) : Fin 16 :=
  (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 13 else 15) else (if i.val < 3 then 9 else 11)) else (if i.val < 6 then (if i.val < 5 then 1 else 0) else (if i.val < 7 then 0 else 1))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 3 else 13) else (if i.val < 11 then 2 else 15)) else (if i.val < 14 then (if i.val < 13 then 1 else 15) else (if i.val < 15 then 0 else 15))))
private def letters (i : Fin 16) : Fin 3 :=
  (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 2 else 2) else (if i.val < 3 then 2 else 2)) else (if i.val < 6 then (if i.val < 5 then 1 else 1) else (if i.val < 7 then 0 else 0))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 2 else 1) else (if i.val < 11 then 2 else 1)) else (if i.val < 14 then (if i.val < 13 then 2 else 0) else (if i.val < 15 then 2 else 0))))
private def nextRow (i : Fin 16) (j : Fin 3) : Fin 16 :=
  ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[6,5,14] else #[7,4,12]) else (if i.val < 3 then #[4,7,10] else #[5,6,8])) else (if i.val < 6 then (if i.val < 5 then #[2,1,11] else #[3,0,9]) else (if i.val < 7 then #[0,3,15] else #[1,2,13]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[10,12,4] else #[11,13,2]) else (if i.val < 11 then #[8,14,5] else #[9,15,3])) else (if i.val < 14 then (if i.val < 13 then #[14,8,6] else #[15,9,0]) else (if i.val < 15 then #[12,10,7] else #[13,11,1])))) : Array (Fin 16))[j.val]!
def prevRow (i : Fin 16) (j : Fin 3) : Fin 16 :=
  ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[6,5,13] else #[7,4,15]) else (if i.val < 3 then #[4,7,9] else #[5,6,11])) else (if i.val < 6 then (if i.val < 5 then #[2,1,8] else #[3,0,10]) else (if i.val < 7 then #[0,3,12] else #[1,2,14]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[10,12,3] else #[11,13,5]) else (if i.val < 11 then #[8,14,2] else #[9,15,4])) else (if i.val < 14 then (if i.val < 13 then #[14,8,1] else #[15,9,7]) else (if i.val < 15 then #[12,10,0] else #[13,11,6])))) : Array (Fin 16))[j.val]!

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

theorem prev_checked : ∀ i j, certificate.next (prevRow i j) j = i :=
  (by decide +kernel)

/-- Executable multiplication and inverse, with laws proved by faithfulness. -/
@[reducible] def group : Group (FiniteGroupRow 16) :=
  certificate.rowGroup rows_injective prevRow prev_checked

/-- Exact identification with the original literal permutation subgroup. -/
def originalEquiv : letI := group
    FiniteGroupRow 16 ≃* Subgroup.closure (Set.range generators) :=
  certificate.rowEquiv rows_injective prevRow prev_checked

end SymmetricSubgroupAsymptotics.BinaryTopSource046
