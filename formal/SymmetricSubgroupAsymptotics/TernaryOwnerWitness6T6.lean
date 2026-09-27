import SymmetricSubgroupAsymptotics.C1FiniteOwnerWitness
import SymmetricSubgroupAsymptotics.TernaryOwnerCayley6T6

/-! Kernel-checked cyclic binary-module owner witness for the literal action 6T6. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section

namespace SymmetricSubgroupAsymptotics.TernaryOwnerWitness6T6

open TernaryOwnerCayley6T6

local instance rowGroup : Group (FiniteGroupRow 24) := group

def base : Subgroup (FiniteGroupRow 24) where
  carrier := {x | x.index = 8 ∨ x.index = 9 ∨ x.index = 10 ∨ x.index = 11 ∨
    x.index = 20 ∨ x.index = 21 ∨ x.index = 22 ∨ x.index = 23}
  one_mem' := by decide +kernel
  mul_mem' := by decide +kernel
  inv_mem' := by decide +kernel

def complement : Subgroup (FiniteGroupRow 24) where
  carrier := {x | x.index = 5 ∨ x.index = 12 ∨ x.index = 23}
  one_mem' := by decide +kernel
  mul_mem' := by decide +kernel
  inv_mem' := by decide +kernel

private instance baseMembership : DecidablePred (fun x => x ∈ base) :=
  fun x => by
    change Decidable (x.index = 8 ∨ x.index = 9 ∨ x.index = 10 ∨ x.index = 11 ∨
      x.index = 20 ∨ x.index = 21 ∨ x.index = 22 ∨ x.index = 23)
    infer_instance

private instance complementMembership : DecidablePred (fun x => x ∈ complement) :=
  fun x => by
    change Decidable (x.index = 5 ∨ x.index = 12 ∨ x.index = 23)
    infer_instance

theorem base_card : Nat.card base = 8 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem complement_card : Nat.card complement = 3 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem base_normal : base.Normal := ⟨by decide +kernel⟩

theorem base_isPGroup : IsPGroup 2 base :=
  IsPGroup.of_card (n := 3) (by simpa using base_card)

theorem complement_isPGroup : IsPGroup 3 complement :=
  IsPGroup.of_card (n := 1) (by simpa using complement_card)

theorem base_exponent_two : ∀ x : base, x ^ 2 = 1 := by
  decide +kernel

theorem complement_exponent_three : ∀ x : complement, x ^ 3 = 1 := by
  decide +kernel

theorem intersection_trivial : ∀ x : FiniteGroupRow 24,
    x ∈ base → x ∈ complement → x = 1 := by
  decide +kernel

def factorBase (x : FiniteGroupRow 24) : base :=
  ⟨⟨(#[22,20,10,8,11,23,10,22,8,9,10,11,23,21,11,9,9,21,8,20,20,21,22,23] :
      Array (Fin 24))[x.index.val]!⟩, by
    rcases x with ⟨i⟩
    fin_cases i <;> decide +kernel⟩

def factorComplement (x : FiniteGroupRow 24) : complement :=
  ⟨⟨(#[12,12,12,12,5,5,5,5,23,23,23,23,12,12,12,12,5,5,5,5,23,23,23,23] :
      Array (Fin 24))[x.index.val]!⟩, by
    rcases x with ⟨i⟩
    fin_cases i <;> decide +kernel⟩

theorem factorization : ∀ x : FiniteGroupRow 24,
    (factorBase x : FiniteGroupRow 24) *
      (factorComplement x : FiniteGroupRow 24) = x := by
  rintro ⟨i⟩
  fin_cases i <;> decide +kernel

def vector : base := ⟨⟨11⟩, by decide +kernel⟩

private def complementElement (j : Fin 3) : complement :=
  ⟨⟨(#[23,5,12] : Array (Fin 24))[j.val]!⟩, by
    fin_cases j <;> decide +kernel⟩

private def cyclicLetters (i : Fin 24) : List (Fin 3) :=
  (#[[],[],[],[],[],[],[],[],[0,1,2],[0,1],[0,2],[0],
      [],[],[],[],[],[],[],[],[1,2],[1],[2],[]] : Array (List (Fin 3)))[i.val]!

def cyclicWord (x : base) : List complement :=
  (cyclicLetters x.1.index).map complementElement

theorem cyclic_word_eq : ∀ x : base,
    ((cyclicWord x).map fun c : complement =>
      normalConjugate base base_normal vector (c : FiniteGroupRow 24)).prod = x := by
  rintro ⟨⟨i⟩, hi⟩
  fin_cases i <;> decide +kernel +revert

def earlierOwner : C1CyclicBinaryModuleOwnerWitness (FiniteGroupRow 24) where
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

end SymmetricSubgroupAsymptotics.TernaryOwnerWitness6T6
