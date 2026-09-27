import SymmetricSubgroupAsymptotics.C1FiniteOwnerWitness
import SymmetricSubgroupAsymptotics.TernaryOwnerCayley6T4

/-! Kernel-checked cyclic binary-module owner witness for the literal action 6T4. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section

namespace SymmetricSubgroupAsymptotics.TernaryOwnerWitness6T4

open TernaryOwnerCayley6T4

local instance rowGroup : Group (FiniteGroupRow 12) := group

def base : Subgroup (FiniteGroupRow 12) where
  carrier := {x | x.index = 4 ∨ x.index = 5 ∨ x.index = 10 ∨ x.index = 11}
  one_mem' := by decide +kernel
  mul_mem' := by decide +kernel
  inv_mem' := by decide +kernel

def complement : Subgroup (FiniteGroupRow 12) where
  carrier := {x | x.index = 2 ∨ x.index = 6 ∨ x.index = 11}
  one_mem' := by decide +kernel
  mul_mem' := by decide +kernel
  inv_mem' := by decide +kernel

private instance baseMembership : DecidablePred (fun x => x ∈ base) :=
  fun x => by
    change Decidable (x.index = 4 ∨ x.index = 5 ∨ x.index = 10 ∨ x.index = 11)
    infer_instance

private instance complementMembership : DecidablePred (fun x => x ∈ complement) :=
  fun x => by
    change Decidable (x.index = 2 ∨ x.index = 6 ∨ x.index = 11)
    infer_instance

theorem base_card : Nat.card base = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem complement_card : Nat.card complement = 3 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem base_normal : base.Normal := ⟨by decide +kernel⟩

theorem base_isPGroup : IsPGroup 2 base :=
  IsPGroup.of_card (n := 2) (by simpa using base_card)

theorem complement_isPGroup : IsPGroup 3 complement :=
  IsPGroup.of_card (n := 1) (by simpa using complement_card)

theorem base_exponent_two : ∀ x : base, x ^ 2 = 1 := by
  decide +kernel

theorem complement_exponent_three : ∀ x : complement, x ^ 3 = 1 := by
  decide +kernel

theorem intersection_trivial : ∀ x : FiniteGroupRow 12,
    x ∈ base → x ∈ complement → x = 1 := by
  decide +kernel

def factorBase (x : FiniteGroupRow 12) : base :=
  ⟨⟨(#[10,5,11,5,4,5,11,4,4,10,10,11] : Array (Fin 12))[x.index.val]!⟩, by
    rcases x with ⟨i⟩
    fin_cases i <;> decide +kernel⟩

def factorComplement (x : FiniteGroupRow 12) : complement :=
  ⟨⟨(#[6,6,2,2,11,11,6,6,2,2,11,11] : Array (Fin 12))[x.index.val]!⟩, by
    rcases x with ⟨i⟩
    fin_cases i <;> decide +kernel⟩

theorem factorization : ∀ x : FiniteGroupRow 12,
    (factorBase x : FiniteGroupRow 12) *
      (factorComplement x : FiniteGroupRow 12) = x := by
  rintro ⟨i⟩
  fin_cases i <;> decide +kernel

def vector : base := ⟨⟨4⟩, by decide +kernel⟩

private def complementElement (j : Fin 3) : complement :=
  ⟨⟨(#[11,2,6] : Array (Fin 12))[j.val]!⟩, by
    fin_cases j <;> decide +kernel⟩

private def cyclicLetters (i : Fin 12) : List (Fin 3) :=
  (#[[],[],[],[],[0],[2],[],[],[],[],[1],[]] : Array (List (Fin 3)))[i.val]!

def cyclicWord (x : base) : List complement :=
  (cyclicLetters x.1.index).map complementElement

theorem cyclic_word_eq : ∀ x : base,
    ((cyclicWord x).map fun c : complement =>
      normalConjugate base base_normal vector (c : FiniteGroupRow 12)).prod = x := by
  rintro ⟨⟨i⟩, hi⟩
  fin_cases i <;> decide +kernel +revert

def earlierOwner : C1CyclicBinaryModuleOwnerWitness (FiniteGroupRow 12) where
  base := base
  complement := complement
  base_normal := base_normal
  basePGroup := base_isPGroup
  complementPGroup := complement_isPGroup
  base_exponent_two := base_exponent_two
  complement_exponent_three := complement_exponent_three
  intersection_trivial := intersection_trivial
  factorBase := factorBase
  factorComplement := factorComplement
  factorization := factorization
  vector := vector
  cyclicWord := cyclicWord
  cyclic_word_eq := cyclic_word_eq

end SymmetricSubgroupAsymptotics.TernaryOwnerWitness6T4
