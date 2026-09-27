import SymmetricSubgroupAsymptotics.FiniteCayleyGroup
import SymmetricSubgroupAsymptotics.FinitePermutationEncoding
import Mathlib.Order.Fin.Basic

/-!
# Literal c=1 high action certificate 6T1

Generated from certificates/data/primitive_rank.jsonl.gz by export_lean_c1_degree_six.py.
Selected transitive row 15; raw-line SHA256 72fa9efa84f03241fc3c3fd0dbbe5c983df25dca5f60448176e1adbcfdb33da4.
All finite equations use Lean's kernel. BFS parents establish actual group
membership; numeric permutation codes establish faithfulness. This proves the literal selected action only;
high-pair coverage and earlier-owner acceptance remain separate theorems.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section

namespace SymmetricSubgroupAsymptotics.TernaryOwnerCayley6T1

private def generator0 : Equiv.Perm (Fin 6) where
  toFun x := (#[1,2,3,4,5,0] : Array (Fin 6))[x.val]!
  invFun x := (#[5,0,1,2,3,4] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def generators (j : Fin 1) : Equiv.Perm (Fin 6) :=
  generator0

private def codes (i : Fin 6) : Fin (6^6) :=
  (if i.val < 3 then (if i.val < 1 then 7465 else (if i.val < 2 then 9020 else 17055)) else (if i.val < 4 then 26170 else (if i.val < 5 then 35465 else 44790)))
private def ranks (i : Fin 6) : ℕ :=
  (if i.val < 3 then (if i.val < 1 then 1 else (if i.val < 2 then 2 else 3)) else (if i.val < 4 then 4 else (if i.val < 5 then 5 else 0)))
private def parents (i : Fin 6) : Fin 6 :=
  (if i.val < 3 then (if i.val < 1 then 5 else (if i.val < 2 then 0 else 1)) else (if i.val < 4 then 2 else (if i.val < 5 then 3 else 5)))
private def letters (i : Fin 6) : Fin 1 :=
  (if i.val < 3 then (if i.val < 1 then 0 else (if i.val < 2 then 0 else 0)) else (if i.val < 4 then 0 else (if i.val < 5 then 0 else 0)))
private def nextRow (i : Fin 6) (j : Fin 1) : Fin 6 :=
  ((if i.val < 3 then (if i.val < 1 then #[1] else (if i.val < 2 then #[2] else #[3])) else (if i.val < 4 then #[4] else (if i.val < 5 then #[5] else #[0]))) : Array (Fin 6))[j.val]!
private def prevRow (i : Fin 6) (j : Fin 1) : Fin 6 :=
  ((if i.val < 3 then (if i.val < 1 then #[5] else (if i.val < 2 then #[0] else #[1])) else (if i.val < 4 then #[2] else (if i.val < 5 then #[3] else #[4]))) : Array (Fin 6))[j.val]!

private theorem parent_lt_checked : ∀ i : Fin 6,
    i ≠ 5 → ranks (parents i) < ranks i := (by decide +kernel)
private theorem parent_next_checked : ∀ i : Fin 6,
    i ≠ 5 → nextRow (parents i) (letters i) = i := (by decide +kernel)

def certificate : EncodedCayleyCertificate
    (permutationGeneratorEncoding generators) 6 where
  rows := codes
  identity := 5
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

theorem exact_card : Nat.card (Subgroup.closure (Set.range generators)) = 6 :=
  certificate.card_closure rows_injective

private theorem prev_checked : ∀ i j, certificate.next (prevRow i j) j = i :=
  (by decide +kernel)

/-- Executable multiplication and inverse, with laws proved by faithfulness. -/
@[reducible] def group : Group (FiniteGroupRow 6) :=
  certificate.rowGroup rows_injective prevRow prev_checked

/-- Exact identification with the original literal permutation subgroup. -/
def originalEquiv : letI := group
    FiniteGroupRow 6 ≃* Subgroup.closure (Set.range generators) :=
  certificate.rowEquiv rows_injective prevRow prev_checked

/-- Exact one-based image lists bind the selected original source tuple. -/
theorem sourceGenerator_images : ∀ j : Fin 1, ∀ x : Fin 6,
    (generators j x).val + 1 =
      ((#[#[2,3,4,5,6,1]] : Array (Array ℕ))[j.val]!)[x.val]! := by
  decide +kernel

end SymmetricSubgroupAsymptotics.TernaryOwnerCayley6T1
