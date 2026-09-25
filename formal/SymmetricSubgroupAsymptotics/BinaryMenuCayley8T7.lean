import SymmetricSubgroupAsymptotics.FiniteCayleyGroup
import SymmetricSubgroupAsymptotics.FinitePermutationEncoding
import Mathlib.Order.Fin.Basic

/-!
# Compact literal action certificate 8T7

Generated from the original menu permutations by export_lean_menu_cayley.py.
All finite equations use Lean's kernel. BFS parents establish actual group
membership; numeric permutation codes establish faithfulness. This certifies
this original action, not finite-menu or normal-registry completeness.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryMenuCayley8T7

private def generator0 : Equiv.Perm (Fin 8) where
  toFun x := (#[1,2,3,4,5,6,7,0] : Array (Fin 8))[x.val]!
  invFun x := (#[7,0,1,2,3,4,5,6] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def generator1 : Equiv.Perm (Fin 8) where
  toFun x := (#[4,1,6,3,0,5,2,7] : Array (Fin 8))[x.val]!
  invFun x := (#[4,1,6,3,0,5,2,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def generators (j : Fin 2) : Equiv.Perm (Fin 8) :=
  (if j.val < 1 then generator0 else generator1)

private def codes (i : Fin 16) : Fin (8^8) :=
  (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 989653 else 2054353) else (if i.val < 3 then 2353946 else 3385886)) else (if i.val < 6 then (if i.val < 5 then 4488547 else 5520487) else (if i.val < 7 then 6852524 else 7917224))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 9245173 else 10309873) else (if i.val < 11 then 10609466 else 11641406)) else (if i.val < 14 then (if i.val < 13 then 13006147 else 14038087) else (if i.val < 15 then 15370124 else 16434824))))
private def ranks (i : Fin 16) : ℕ :=
  (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 4 else 1) else (if i.val < 3 then 3 else 7)) else (if i.val < 6 then (if i.val < 5 then 6 else 11) else (if i.val < 7 then 10 else 14))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 9 else 5) else (if i.val < 11 then 8 else 13)) else (if i.val < 14 then (if i.val < 13 then 12 else 15) else (if i.val < 15 then 2 else 0))))
private def parents (i : Fin 16) : Fin 16 :=
  (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 1 else 15) else (if i.val < 3 then 1 else 2)) else (if i.val < 6 then (if i.val < 5 then 2 else 4) else (if i.val < 7 then 4 else 6))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 9 else 14) else (if i.val < 11 then 0 else 10)) else (if i.val < 14 then (if i.val < 13 then 3 else 12) else (if i.val < 15 then 15 else 15))))
private def letters (i : Fin 16) : Fin 2 :=
  (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 1 else 0) else (if i.val < 3 then 0 else 1)) else (if i.val < 6 then (if i.val < 5 then 0 else 1) else (if i.val < 7 then 0 else 1))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 1 else 0) else (if i.val < 11 then 0 else 1)) else (if i.val < 14 then (if i.val < 13 then 0 else 1) else (if i.val < 15 then 1 else 0))))
private def nextRow (i : Fin 16) (j : Fin 2) : Fin 16 :=
  ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[10,1] else #[2,0]) else (if i.val < 3 then #[4,3] else #[12,2])) else (if i.val < 6 then (if i.val < 5 then #[6,5] else #[14,4]) else (if i.val < 7 then #[8,7] else #[0,6]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[11,9] else #[3,8]) else (if i.val < 11 then #[5,11] else #[13,10])) else (if i.val < 14 then (if i.val < 13 then #[7,13] else #[15,12]) else (if i.val < 15 then #[9,15] else #[1,14])))) : Array (Fin 16))[j.val]!
private def prevRow (i : Fin 16) (j : Fin 2) : Fin 16 :=
  ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[7,1] else #[15,0]) else (if i.val < 3 then #[1,3] else #[9,2])) else (if i.val < 6 then (if i.val < 5 then #[2,5] else #[10,4]) else (if i.val < 7 then #[4,7] else #[12,6]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[6,9] else #[14,8]) else (if i.val < 11 then #[0,11] else #[8,10])) else (if i.val < 14 then (if i.val < 13 then #[3,13] else #[11,12]) else (if i.val < 15 then #[5,15] else #[13,14])))) : Array (Fin 16))[j.val]!

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

end SymmetricSubgroupAsymptotics.BinaryMenuCayley8T7
