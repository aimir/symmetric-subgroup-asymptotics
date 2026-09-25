import SymmetricSubgroupAsymptotics.FiniteCayleyGroup
import SymmetricSubgroupAsymptotics.FinitePermutationEncoding
import Mathlib.Order.Fin.Basic

/-!
# Compact literal action certificate 2T1

Generated from the original menu permutations by export_lean_menu_cayley.py.
All finite equations use Lean's kernel. BFS parents establish actual group
membership; numeric permutation codes establish faithfulness. This certifies
this original action, not finite-menu or normal-registry completeness.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryMenuCayley2T1

private def generator0 : Equiv.Perm (Fin 2) where
  toFun x := (#[1,0] : Array (Fin 2))[x.val]!
  invFun x := (#[1,0] : Array (Fin 2))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def generators (j : Fin 1) : Equiv.Perm (Fin 2) :=
  generator0

private def codes (i : Fin 2) : Fin (2^2) :=
  (if i.val < 1 then 1 else 2)
private def ranks (i : Fin 2) : ℕ :=
  (if i.val < 1 then 1 else 0)
private def parents (i : Fin 2) : Fin 2 :=
  (if i.val < 1 then 1 else 1)
private def letters (i : Fin 2) : Fin 1 :=
  (if i.val < 1 then 0 else 0)
private def nextRow (i : Fin 2) (j : Fin 1) : Fin 2 :=
  ((if i.val < 1 then #[1] else #[0]) : Array (Fin 2))[j.val]!
private def prevRow (i : Fin 2) (j : Fin 1) : Fin 2 :=
  ((if i.val < 1 then #[1] else #[0]) : Array (Fin 2))[j.val]!

private theorem parent_lt_checked : ∀ i : Fin 2,
    i ≠ 1 → ranks (parents i) < ranks i := (by decide +kernel)
private theorem parent_next_checked : ∀ i : Fin 2,
    i ≠ 1 → nextRow (parents i) (letters i) = i := (by decide +kernel)

def certificate : EncodedCayleyCertificate
    (permutationGeneratorEncoding generators) 2 where
  rows := codes
  identity := 1
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

theorem exact_card : Nat.card (Subgroup.closure (Set.range generators)) = 2 :=
  certificate.card_closure rows_injective

private theorem prev_checked : ∀ i j, certificate.next (prevRow i j) j = i :=
  (by decide +kernel)

/-- Executable multiplication and inverse, with laws proved by faithfulness. -/
@[reducible] def group : Group (FiniteGroupRow 2) :=
  certificate.rowGroup rows_injective prevRow prev_checked

/-- Exact identification with the original literal permutation subgroup. -/
def originalEquiv : letI := group
    FiniteGroupRow 2 ≃* Subgroup.closure (Set.range generators) :=
  certificate.rowEquiv rows_injective prevRow prev_checked

end SymmetricSubgroupAsymptotics.BinaryMenuCayley2T1
