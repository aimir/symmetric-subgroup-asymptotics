import SymmetricSubgroupAsymptotics.C1FiniteOwnerWitness
import SymmetricSubgroupAsymptotics.TernaryOwnerCayley6T5

/-! Kernel-checked odd-index-two owner witness for the literal action 6T5. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section

namespace SymmetricSubgroupAsymptotics.TernaryOwnerWitness6T5

open TernaryOwnerCayley6T5

local instance rowGroup : Group (FiniteGroupRow 18) := group

def ternary : Subgroup (FiniteGroupRow 18) where
  carrier := {x | x.index = 3 ∨ x.index = 4 ∨ x.index = 5 ∨
    x.index = 9 ∨ x.index = 10 ∨ x.index = 11 ∨
    x.index = 15 ∨ x.index = 16 ∨ x.index = 17}
  one_mem' := by decide +kernel
  mul_mem' := by decide +kernel
  inv_mem' := by decide +kernel

private instance ternaryMembership : DecidablePred (fun x => x ∈ ternary) :=
  fun x => by
    change Decidable (x.index = 3 ∨ x.index = 4 ∨ x.index = 5 ∨
      x.index = 9 ∨ x.index = 10 ∨ x.index = 11 ∨
      x.index = 15 ∨ x.index = 16 ∨ x.index = 17)
    infer_instance

theorem ternary_card : Nat.card ternary = 9 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem ternary_normal : ternary.Normal :=
  ⟨by decide +kernel⟩

theorem ternary_isPGroup : IsPGroup 3 ternary :=
  IsPGroup.of_card (n := 2) (by simpa using ternary_card)

theorem ternary_index : ternary.index = 2 := by
  have h := ternary.card_mul_index
  rw [ternary_card] at h
  have hG : Nat.card (FiniteGroupRow 18) = 18 := by
    rw [Nat.card_eq_fintype_card]
    rfl
  omega

def earlierOwner : C1OddIndexTwoOwnerWitness (FiniteGroupRow 18) where
  ternary := ternary
  normal := ternary_normal
  ternaryPGroup := ternary_isPGroup
  index_two := ternary_index

end SymmetricSubgroupAsymptotics.TernaryOwnerWitness6T5
