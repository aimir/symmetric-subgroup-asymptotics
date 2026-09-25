import SymmetricSubgroupAsymptotics.FiniteCayleyGroup
import SymmetricSubgroupAsymptotics.FinitePermutationEncoding
import Mathlib.Order.Fin.Basic

/-!
# Compact literal action certificate 4T1

Generated from the original menu permutations by export_lean_menu_cayley.py.
All finite equations use Lean's kernel. BFS parents establish actual group
membership; numeric permutation codes establish faithfulness. This certifies
this original action, not finite-menu or normal-registry completeness.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryMenuCayley4T1

private def generator0 : Equiv.Perm (Fin 4) where
  toFun x := (#[1,2,3,0] : Array (Fin 4))[x.val]!
  invFun x := (#[3,0,1,2] : Array (Fin 4))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def generators (j : Fin 1) : Equiv.Perm (Fin 4) :=
  generator0

private def codes (i : Fin 4) : Fin (4^4) :=
  (if i.val < 2 then (if i.val < 1 then 57 else 78) else (if i.val < 3 then 147 else 228))
private def ranks (i : Fin 4) : ℕ :=
  (if i.val < 2 then (if i.val < 1 then 1 else 2) else (if i.val < 3 then 3 else 0))
private def parents (i : Fin 4) : Fin 4 :=
  (if i.val < 2 then (if i.val < 1 then 3 else 0) else (if i.val < 3 then 1 else 3))
private def letters (i : Fin 4) : Fin 1 :=
  (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 0))
private def nextRow (i : Fin 4) (j : Fin 1) : Fin 4 :=
  ((if i.val < 2 then (if i.val < 1 then #[1] else #[2]) else (if i.val < 3 then #[3] else #[0])) : Array (Fin 4))[j.val]!
private def prevRow (i : Fin 4) (j : Fin 1) : Fin 4 :=
  ((if i.val < 2 then (if i.val < 1 then #[3] else #[0]) else (if i.val < 3 then #[1] else #[2])) : Array (Fin 4))[j.val]!

private theorem parent_lt_checked : ∀ i : Fin 4,
    i ≠ 3 → ranks (parents i) < ranks i := (by decide +kernel)
private theorem parent_next_checked : ∀ i : Fin 4,
    i ≠ 3 → nextRow (parents i) (letters i) = i := (by decide +kernel)

def certificate : EncodedCayleyCertificate
    (permutationGeneratorEncoding generators) 4 where
  rows := codes
  identity := 3
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

theorem exact_card : Nat.card (Subgroup.closure (Set.range generators)) = 4 :=
  certificate.card_closure rows_injective

private theorem prev_checked : ∀ i j, certificate.next (prevRow i j) j = i :=
  (by decide +kernel)

/-- Executable multiplication and inverse, with laws proved by faithfulness. -/
@[reducible] def group : Group (FiniteGroupRow 4) :=
  certificate.rowGroup rows_injective prevRow prev_checked

/-- Exact identification with the original literal permutation subgroup. -/
def originalEquiv : letI := group
    FiniteGroupRow 4 ≃* Subgroup.closure (Set.range generators) :=
  certificate.rowEquiv rows_injective prevRow prev_checked

end SymmetricSubgroupAsymptotics.BinaryMenuCayley4T1
