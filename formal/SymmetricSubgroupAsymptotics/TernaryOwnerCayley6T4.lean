import SymmetricSubgroupAsymptotics.FiniteCayleyGroup
import SymmetricSubgroupAsymptotics.FinitePermutationEncoding
import Mathlib.Order.Fin.Basic

/-!
# Literal c=1 high action certificate 6T4

Generated from certificates/data/primitive_rank.jsonl.gz by export_lean_c1_degree_six.py.
Selected transitive row 18; raw-line SHA256 21306910c50b285fa8f21c3b08909892974a92804fa03ceacd4131d199261dec.
All finite equations use Lean's kernel. BFS parents establish actual group
membership; numeric permutation codes establish faithfulness. This proves the literal selected action only;
high-pair coverage and earlier-owner acceptance remain separate theorems.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section

namespace SymmetricSubgroupAsymptotics.TernaryOwnerCayley6T4

private def generator0 : Equiv.Perm (Fin 6) where
  toFun x := (#[3,4,2,0,1,5] : Array (Fin 6))[x.val]!
  invFun x := (#[3,4,2,0,1,5] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def generator1 : Equiv.Perm (Fin 6) where
  toFun x := (#[2,3,4,5,0,1] : Array (Fin 6))[x.val]!
  invFun x := (#[4,5,0,1,2,3] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def generators (j : Fin 2) : Equiv.Perm (Fin 6) :=
  (if j.val < 1 then generator0 else generator1)

private def codes (i : Fin 12) : Fin (6^6) :=
  (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then 3595 else (if i.val < 2 then 6820 else 9020)) else (if i.val < 4 then 12245 else (if i.val < 5 then 17700 else 20925))) else (if i.val < 9 then (if i.val < 7 then 26170 else (if i.val < 8 then 30685 else 31595)) else (if i.val < 10 then 36110 else (if i.val < 11 then 40275 else 44790))))
private def ranks (i : Fin 12) : ℕ :=
  (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then 7 else (if i.val < 2 then 8 else 2)) else (if i.val < 4 then 4 else (if i.val < 5 then 11 else 10))) else (if i.val < 9 then (if i.val < 7 then 5 else (if i.val < 8 then 9 else 6)) else (if i.val < 10 then 3 else (if i.val < 11 then 1 else 0))))
private def parents (i : Fin 12) : Fin 12 :=
  (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then 9 else (if i.val < 2 then 3 else 11)) else (if i.val < 4 then 2 else (if i.val < 5 then 7 else 1))) else (if i.val < 9 then (if i.val < 7 then 2 else (if i.val < 8 then 6 else 9)) else (if i.val < 10 then 10 else (if i.val < 11 then 11 else 11))))
private def letters (i : Fin 12) : Fin 2 :=
  (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then 1 else (if i.val < 2 then 1 else 1)) else (if i.val < 4 then 0 else (if i.val < 5 then 1 else 1))) else (if i.val < 9 then (if i.val < 7 then 1 else (if i.val < 8 then 0 else 0)) else (if i.val < 10 then 1 else (if i.val < 11 then 0 else 0))))
private def nextRow (i : Fin 12) (j : Fin 2) : Fin 12 :=
  ((if i.val < 6 then (if i.val < 3 then (if i.val < 1 then #[1,10] else (if i.val < 2 then #[0,5] else #[3,6])) else (if i.val < 4 then #[2,1] else (if i.val < 5 then #[5,8] else #[4,3]))) else (if i.val < 9 then (if i.val < 7 then #[7,11] else (if i.val < 8 then #[6,4] else #[9,7])) else (if i.val < 10 then #[8,0] else (if i.val < 11 then #[11,9] else #[10,2])))) : Array (Fin 12))[j.val]!
private def prevRow (i : Fin 12) (j : Fin 2) : Fin 12 :=
  ((if i.val < 6 then (if i.val < 3 then (if i.val < 1 then #[1,9] else (if i.val < 2 then #[0,3] else #[3,11])) else (if i.val < 4 then #[2,5] else (if i.val < 5 then #[5,7] else #[4,1]))) else (if i.val < 9 then (if i.val < 7 then #[7,2] else (if i.val < 8 then #[6,8] else #[9,4])) else (if i.val < 10 then #[8,10] else (if i.val < 11 then #[11,0] else #[10,6])))) : Array (Fin 12))[j.val]!

private theorem parent_lt_checked : ∀ i : Fin 12,
    i ≠ 11 → ranks (parents i) < ranks i := (by decide +kernel)
private theorem parent_next_checked : ∀ i : Fin 12,
    i ≠ 11 → nextRow (parents i) (letters i) = i := (by decide +kernel)

def certificate : EncodedCayleyCertificate
    (permutationGeneratorEncoding generators) 12 where
  rows := codes
  identity := 11
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

theorem exact_card : Nat.card (Subgroup.closure (Set.range generators)) = 12 :=
  certificate.card_closure rows_injective

private theorem prev_checked : ∀ i j, certificate.next (prevRow i j) j = i :=
  (by decide +kernel)

/-- Executable multiplication and inverse, with laws proved by faithfulness. -/
@[reducible] def group : Group (FiniteGroupRow 12) :=
  certificate.rowGroup rows_injective prevRow prev_checked

/-- Exact identification with the original literal permutation subgroup. -/
def originalEquiv : letI := group
    FiniteGroupRow 12 ≃* Subgroup.closure (Set.range generators) :=
  certificate.rowEquiv rows_injective prevRow prev_checked

/-- Exact one-based image lists bind the selected original source tuple. -/
theorem sourceGenerator_images : ∀ j : Fin 2, ∀ x : Fin 6,
    (generators j x).val + 1 =
      ((#[#[4,5,3,1,2,6],#[3,4,5,6,1,2]] : Array (Array ℕ))[j.val]!)[x.val]! := by
  decide +kernel

end SymmetricSubgroupAsymptotics.TernaryOwnerCayley6T4
