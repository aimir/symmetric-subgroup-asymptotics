import SymmetricSubgroupAsymptotics.FiniteCayleyGroup
import SymmetricSubgroupAsymptotics.FinitePermutationEncoding
import Mathlib.Order.Fin.Basic

/-!
# Compact literal action certificate 8T4

Generated from the original menu permutations by export_lean_menu_cayley.py.
All finite equations use Lean's kernel. BFS parents establish actual group
membership; numeric permutation codes establish faithfulness. This certifies
this original action, not finite-menu or normal-registry completeness.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryMenuCayley8T4

private def generator0 : Equiv.Perm (Fin 8) where
  toFun x := (#[1,2,7,4,5,6,3,0] : Array (Fin 8))[x.val]!
  invFun x := (#[7,0,1,6,3,4,5,2] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def generator1 : Equiv.Perm (Fin 8) where
  toFun x := (#[5,4,3,2,1,0,7,6] : Array (Fin 8))[x.val]!
  invFun x := (#[5,4,3,2,1,0,7,6] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def generators (j : Fin 2) : Equiv.Perm (Fin 8) :=
  (if j.val < 1 then generator0 else generator1)

private def codes (i : Fin 8) : Fin (8^8) :=
  (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 1006033 else 3271226) else (if i.val < 3 then 5651527 else 6336302)) else (if i.val < 6 then (if i.val < 5 then 8745331 else 11240348) else (if i.val < 7 then 14423269 else 16434824)))
private def ranks (i : Fin 8) : ℕ :=
  (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 1 else 3) else (if i.val < 3 then 6 else 4)) else (if i.val < 6 then (if i.val < 5 then 7 else 5) else (if i.val < 7 then 2 else 0)))
private def parents (i : Fin 8) : Fin 8 :=
  (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 7 else 0) else (if i.val < 3 then 1 else 0)) else (if i.val < 6 then (if i.val < 5 then 1 else 6) else (if i.val < 7 then 7 else 7)))
private def letters (i : Fin 8) : Fin 2 :=
  (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 1)) else (if i.val < 6 then (if i.val < 5 then 1 else 0) else (if i.val < 7 then 1 else 0)))
private def nextRow (i : Fin 8) (j : Fin 2) : Fin 8 :=
  ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,3] else #[2,4]) else (if i.val < 3 then #[7,5] else #[6,0])) else (if i.val < 6 then (if i.val < 5 then #[3,1] else #[4,2]) else (if i.val < 7 then #[5,7] else #[0,6]))) : Array (Fin 8))[j.val]!
private def prevRow (i : Fin 8) (j : Fin 2) : Fin 8 :=
  ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[7,3] else #[0,4]) else (if i.val < 3 then #[1,5] else #[4,0])) else (if i.val < 6 then (if i.val < 5 then #[5,1] else #[6,2]) else (if i.val < 7 then #[3,7] else #[2,6]))) : Array (Fin 8))[j.val]!

private theorem parent_lt_checked : ∀ i : Fin 8,
    i ≠ 7 → ranks (parents i) < ranks i := (by decide +kernel)
private theorem parent_next_checked : ∀ i : Fin 8,
    i ≠ 7 → nextRow (parents i) (letters i) = i := (by decide +kernel)

def certificate : EncodedCayleyCertificate
    (permutationGeneratorEncoding generators) 8 where
  rows := codes
  identity := 7
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

theorem exact_card : Nat.card (Subgroup.closure (Set.range generators)) = 8 :=
  certificate.card_closure rows_injective

private theorem prev_checked : ∀ i j, certificate.next (prevRow i j) j = i :=
  (by decide +kernel)

/-- Executable multiplication and inverse, with laws proved by faithfulness. -/
@[reducible] def group : Group (FiniteGroupRow 8) :=
  certificate.rowGroup rows_injective prevRow prev_checked

/-- Exact identification with the original literal permutation subgroup. -/
def originalEquiv : letI := group
    FiniteGroupRow 8 ≃* Subgroup.closure (Set.range generators) :=
  certificate.rowEquiv rows_injective prevRow prev_checked

end SymmetricSubgroupAsymptotics.BinaryMenuCayley8T4
