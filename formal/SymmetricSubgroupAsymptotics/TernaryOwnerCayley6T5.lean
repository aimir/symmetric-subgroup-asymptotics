import SymmetricSubgroupAsymptotics.FiniteCayleyGroup
import SymmetricSubgroupAsymptotics.FinitePermutationEncoding
import Mathlib.Order.Fin.Basic

/-!
# Literal c=1 high action certificate 6T5

Generated from certificates/data/primitive_rank.jsonl.gz by export_lean_c1_degree_six.py.
Selected transitive row 19; raw-line SHA256 adad265bce689c8843f462c8ead65093d125a7f1617c91f943f3bae2bc5e1d56.
All finite equations use Lean's kernel. BFS parents establish actual group
membership; numeric permutation codes establish faithfulness. This proves the literal selected action only;
high-pair coverage and earlier-owner acceptance remain separate theorems.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section

namespace SymmetricSubgroupAsymptotics.TernaryOwnerCayley6T5

private def generator0 : Equiv.Perm (Fin 6) where
  toFun x := (#[0,3,2,5,4,1] : Array (Fin 6))[x.val]!
  invFun x := (#[0,5,2,1,4,3] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def generator1 : Equiv.Perm (Fin 6) where
  toFun x := (#[3,4,5,0,1,2] : Array (Fin 6))[x.val]!
  invFun x := (#[3,4,5,0,1,2] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def generators (j : Fin 2) : Equiv.Perm (Fin 6) :=
  (if j.val < 1 then generator0 else generator1)

private def codes (i : Fin 18) : Fin (6^6) :=
  (if i.val < 9 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 2355 else 4805) else (if i.val < 3 then 7465 else 9020)) else (if i.val < 6 then (if i.val < 5 then 11470 else 14130) else (if i.val < 7 then 17055 else (if i.val < 8 then 19505 else 22165)))) else (if i.val < 13 then (if i.val < 11 then (if i.val < 10 then 23720 else 26170) else (if i.val < 12 then 28830 else 33015)) else (if i.val < 15 then (if i.val < 14 then 35465 else 38125) else (if i.val < 16 then 39680 else (if i.val < 17 then 42130 else 44790)))))
private def ranks (i : Fin 18) : ℕ :=
  (if i.val < 9 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 8 else 11) else (if i.val < 3 then 14 else 12)) else (if i.val < 6 then (if i.val < 5 then 16 else 1) else (if i.val < 7 then 2 else (if i.val < 8 then 4 else 6)))) else (if i.val < 13 then (if i.val < 11 then (if i.val < 10 then 15 else 17) else (if i.val < 12 then 3 else 5)) else (if i.val < 15 then (if i.val < 14 then 7 else 10) else (if i.val < 16 then 9 else (if i.val < 17 then 13 else 0)))))
private def parents (i : Fin 18) : Fin 18 :=
  (if i.val < 9 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 12 else 13) else (if i.val < 3 then 14 else 13)) else (if i.val < 6 then (if i.val < 5 then 1 else 17) else (if i.val < 7 then 17 else (if i.val < 8 then 5 else 11)))) else (if i.val < 13 then (if i.val < 11 then (if i.val < 10 then 14 else 2) else (if i.val < 12 then 5 else 6)) else (if i.val < 15 then (if i.val < 14 then 7 else 8) else (if i.val < 16 then 12 else (if i.val < 17 then 0 else 17)))))
private def letters (i : Fin 18) : Fin 2 :=
  (if i.val < 9 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 1)) else (if i.val < 6 then (if i.val < 5 then 1 else 0) else (if i.val < 7 then 1 else (if i.val < 8 then 1 else 1)))) else (if i.val < 13 then (if i.val < 11 then (if i.val < 10 then 1 else 1) else (if i.val < 12 then 0 else 0)) else (if i.val < 15 then (if i.val < 14 then 0 else 0) else (if i.val < 16 then 1 else (if i.val < 17 then 1 else 0)))))
private def nextRow (i : Fin 18) (j : Fin 2) : Fin 18 :=
  ((if i.val < 9 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[6,16] else #[7,4]) else (if i.val < 3 then #[8,10] else #[9,13])) else (if i.val < 6 then (if i.val < 5 then #[10,1] else #[11,7]) else (if i.val < 7 then #[12,17] else (if i.val < 8 then #[13,5] else #[14,11])))) else (if i.val < 13 then (if i.val < 11 then (if i.val < 10 then #[15,14] else #[16,2]) else (if i.val < 12 then #[17,8] else #[0,15])) else (if i.val < 15 then (if i.val < 14 then #[1,3] else #[2,9]) else (if i.val < 16 then #[3,12] else (if i.val < 17 then #[4,0] else #[5,6]))))) : Array (Fin 18))[j.val]!
private def prevRow (i : Fin 18) (j : Fin 2) : Fin 18 :=
  ((if i.val < 9 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[12,16] else #[13,4]) else (if i.val < 3 then #[14,10] else #[15,13])) else (if i.val < 6 then (if i.val < 5 then #[16,1] else #[17,7]) else (if i.val < 7 then #[0,17] else (if i.val < 8 then #[1,5] else #[2,11])))) else (if i.val < 13 then (if i.val < 11 then (if i.val < 10 then #[3,14] else #[4,2]) else (if i.val < 12 then #[5,8] else #[6,15])) else (if i.val < 15 then (if i.val < 14 then #[7,3] else #[8,9]) else (if i.val < 16 then #[9,12] else (if i.val < 17 then #[10,0] else #[11,6]))))) : Array (Fin 18))[j.val]!

private theorem parent_lt_checked : ∀ i : Fin 18,
    i ≠ 17 → ranks (parents i) < ranks i := (Fin.addCases (m := 9) (n := 9) (by decide +kernel) (by decide +kernel))
private theorem parent_next_checked : ∀ i : Fin 18,
    i ≠ 17 → nextRow (parents i) (letters i) = i := (Fin.addCases (m := 9) (n := 9) (by decide +kernel) (by decide +kernel))

def certificate : EncodedCayleyCertificate
    (permutationGeneratorEncoding generators) 18 where
  rows := codes
  identity := 17
  identity_eq := by decide +kernel
  next := nextRow
  next_eq := (Fin.addCases (m := 9) (n := 9) (by decide +kernel) (by decide +kernel))
  rank := ranks
  parent i _ := parents i
  letter i _ := letters i
  parent_lt := parent_lt_checked
  parent_next := parent_next_checked

private theorem codes_strict : StrictMono codes :=
  Fin.strictMono_iff_lt_succ.mpr (Fin.addCases (m := 8) (n := 9) (by decide +kernel) (by decide +kernel))

theorem rows_injective : Function.Injective certificate.rows := codes_strict.injective

theorem exact_card : Nat.card (Subgroup.closure (Set.range generators)) = 18 :=
  certificate.card_closure rows_injective

private theorem prev_checked : ∀ i j, certificate.next (prevRow i j) j = i :=
  (Fin.addCases (m := 9) (n := 9) (by decide +kernel) (by decide +kernel))

/-- Executable multiplication and inverse, with laws proved by faithfulness. -/
@[reducible] def group : Group (FiniteGroupRow 18) :=
  certificate.rowGroup rows_injective prevRow prev_checked

/-- Exact identification with the original literal permutation subgroup. -/
def originalEquiv : letI := group
    FiniteGroupRow 18 ≃* Subgroup.closure (Set.range generators) :=
  certificate.rowEquiv rows_injective prevRow prev_checked

/-- Exact one-based image lists bind the selected original source tuple. -/
theorem sourceGenerator_images : ∀ j : Fin 2, ∀ x : Fin 6,
    (generators j x).val + 1 =
      ((#[#[1,4,3,6,5,2],#[4,5,6,1,2,3]] : Array (Array ℕ))[j.val]!)[x.val]! := by
  decide +kernel

end SymmetricSubgroupAsymptotics.TernaryOwnerCayley6T5
