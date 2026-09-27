import SymmetricSubgroupAsymptotics.C1FiniteOwnerWitness
import SymmetricSubgroupAsymptotics.TernaryOwnerCayley6T1

/-! Kernel-checked odd-index-two owner witness for the literal action 6T1. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section

namespace SymmetricSubgroupAsymptotics.TernaryOwnerWitness6T1

open TernaryOwnerCayley6T1

local instance rowGroup : Group (FiniteGroupRow 6) := group

def ternary : Subgroup (FiniteGroupRow 6) where
  carrier := {x | x.index = 1 ∨ x.index = 3 ∨ x.index = 5}
  one_mem' := by decide +kernel
  mul_mem' := by decide +kernel
  inv_mem' := by decide +kernel

private instance ternaryMembership : DecidablePred (fun x => x ∈ ternary) :=
  fun x => by
    change Decidable (x.index = 1 ∨ x.index = 3 ∨ x.index = 5)
    infer_instance

theorem ternary_card : Nat.card ternary = 3 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem ternary_normal : ternary.Normal :=
  ⟨by decide +kernel⟩

theorem ternary_isPGroup : IsPGroup 3 ternary :=
  IsPGroup.of_card (n := 1) (by simpa using ternary_card)

theorem ternary_index : ternary.index = 2 := by
  have h := ternary.card_mul_index
  rw [ternary_card] at h
  have hG : Nat.card (FiniteGroupRow 6) = 6 := by
    rw [Nat.card_eq_fintype_card]
    rfl
  omega

def earlierOwner : C1OddIndexTwoOwnerWitness (FiniteGroupRow 6) where
  ternary := ternary
  normal := ternary_normal
  ternaryPGroup := ternary_isPGroup
  index_two := ternary_index

end SymmetricSubgroupAsymptotics.TernaryOwnerWitness6T1
