import SymmetricSubgroupAsymptotics.BinaryNormalGeneratorChecks
import SymmetricSubgroupAsymptotics.FiniteCentralizerRowCoordinates
import SymmetricSubgroupAsymptotics.FinitePermutationEncoding
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.FinCases

/-!
# Selected six-pair action 23: Cayley base

This is a resource-bounded split of the selected action-23 certificate.
All finite equations remain kernel checked.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction023ClassPilot

private def generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[10,11,6,7,2,3,4,5,0,1,8,9] : Array (Fin 12))[x.val]!
  invFun x := (#[8,9,4,5,6,7,2,3,10,11,0,1] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[1,0,9,8,10,11,7,6,3,2,4,5] : Array (Fin 12))[x.val]!
  invFun x := (#[1,0,9,8,10,11,7,6,3,2,4,5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[6,7,3,2,11,10,0,1,9,8,5,4] : Array (Fin 12))[x.val]!
  invFun x := (#[6,7,3,2,11,10,0,1,9,8,5,4] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def generators (j : Fin 3) : Equiv.Perm (Fin 12) :=
  (if j.val < 1 then generator0 else (if j.val < 2 then generator1 else generator2))

private def codes (i : Fin 12) : Fin (12^12) :=
  (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then 89751379707 else (if i.val < 2 then 804181114484 else 1672625014192)) else (if i.val < 4 then 2386989057299 else (if i.val < 5 then 3326806934154 else 3974559668497))) else (if i.val < 9 then (if i.val < 7 then 4948145778422 else (if i.val < 8 then 5595432699417 else 6540413321717)) else (if i.val < 10 then 7187765934382 else (if i.val < 11 then 8127518119567 else 8842413667692))))

private def ranks (i : Fin 12) : ℕ :=
  (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then 11 else (if i.val < 2 then 4 else 6)) else (if i.val < 4 then 5 else (if i.val < 5 then 3 else 2))) else (if i.val < 9 then (if i.val < 7 then 10 else (if i.val < 8 then 9 else 8)) else (if i.val < 10 then 1 else (if i.val < 11 then 7 else 0))))

private def parents (i : Fin 12) : Fin 12 :=
  (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then 2 else (if i.val < 2 then 9 else 9)) else (if i.val < 4 then 9 else (if i.val < 5 then 11 else 11))) else (if i.val < 9 then (if i.val < 7 then 1 else (if i.val < 8 then 1 else 4)) else (if i.val < 10 then 11 else (if i.val < 11 then 5 else 11))))

private def letters (i : Fin 12) : Fin 3 :=
  (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then 0 else (if i.val < 2 then 0 else 2)) else (if i.val < 4 then 1 else (if i.val < 5 then 2 else 1))) else (if i.val < 9 then (if i.val < 7 then 2 else (if i.val < 8 then 1 else 0)) else (if i.val < 10 then 0 else (if i.val < 11 then 2 else 0))))

private def nextRow (i : Fin 12) (j : Fin 3) : Fin 12 :=
  ((if i.val < 6 then (if i.val < 3 then (if i.val < 1 then #[5,6,7] else (if i.val < 2 then #[11,7,6] else #[0,8,9])) else (if i.val < 4 then #[6,9,8] else (if i.val < 5 then #[8,10,11] else #[2,11,10]))) else (if i.val < 9 then (if i.val < 7 then #[10,0,1] else (if i.val < 8 then #[4,1,0] else #[7,2,3])) else (if i.val < 10 then #[1,3,2] else (if i.val < 11 then #[3,4,5] else #[9,5,4])))) : Array (Fin 12))[j.val]!

private def prevRow (i : Fin 12) (j : Fin 3) : Fin 12 :=
  ((if i.val < 6 then (if i.val < 3 then (if i.val < 1 then #[2,6,7] else (if i.val < 2 then #[9,7,6] else #[5,8,9])) else (if i.val < 4 then #[10,9,8] else (if i.val < 5 then #[7,10,11] else #[0,11,10]))) else (if i.val < 9 then (if i.val < 7 then #[3,0,1] else (if i.val < 8 then #[8,1,0] else #[4,2,3])) else (if i.val < 10 then #[11,3,2] else (if i.val < 11 then #[6,4,5] else #[1,5,4])))) : Array (Fin 12))[j.val]!

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

theorem rows_injective : Function.Injective certificate.rows :=
  codes_strict.injective

theorem exact_card :
    Nat.card (Subgroup.closure (Set.range generators)) = 12 :=
  certificate.card_closure rows_injective

private theorem prev_checked : ∀ i j,
    certificate.next (prevRow i j) j = i := (by decide +kernel)

@[reducible] def group : Group (FiniteGroupRow 12) :=
  certificate.rowGroup rows_injective prevRow prev_checked

def originalEquiv : letI := group
    FiniteGroupRow 12 ≃* Subgroup.closure (Set.range generators) :=
  certificate.rowEquiv rows_injective prevRow prev_checked

abbrev Source := FiniteGroupRow 12

instance selectedSourceGroup : Group Source := group

def ambient (j : Fin 3) : Source :=
  ⟨certificate.next certificate.identity j⟩

theorem ambient_full : Subgroup.closure (Set.range ambient) = ⊤ :=
  certificate.row_generators_full rows_injective prevRow prev_checked

theorem source_card : Nat.card Source = 12 := by
  rw [Nat.card_eq_fintype_card]
  rfl
end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction023ClassPilot

end
