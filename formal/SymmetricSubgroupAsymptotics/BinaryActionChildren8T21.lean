import SymmetricSubgroupAsymptotics.BinaryActionRegistry8

/-! All original index-two transitive children of b8_21, checked by generator bits. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryActionChildren8T21
open BinaryActionRegistry8
private def C := BinaryMenuCayley8T21.certificate
private def values (bits : Fin 3 → Bool) (i : Fin 32) : Bool :=
  (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then (true == bits 1) else ((true == bits 0) == bits 1)) else (if i.val < 3 then ((true == bits 0) == bits 1) else (true == bits 1))) else (if i.val < 6 then (if i.val < 5 then ((true == bits 0) == bits 2) else (true == bits 2)) else (if i.val < 7 then (true == bits 2) else (true == bits 2)))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then ((true == bits 1) == bits 2) else ((true == bits 1) == bits 2)) else (if i.val < 11 then ((true == bits 1) == bits 2) else ((true == bits 1) == bits 2))) else (if i.val < 14 then (if i.val < 13 then true else (true == bits 0)) else (if i.val < 15 then (true == bits 0) else true)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then (true == bits 1) else ((true == bits 0) == bits 1)) else (if i.val < 19 then ((true == bits 0) == bits 1) else (true == bits 1))) else (if i.val < 22 then (if i.val < 21 then ((true == bits 0) == bits 2) else (true == bits 2)) else (if i.val < 23 then (true == bits 2) else (true == bits 2)))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then (((true == bits 0) == bits 1) == bits 2) else ((true == bits 1) == bits 2)) else (if i.val < 27 then (((true == bits 0) == bits 1) == bits 2) else ((true == bits 1) == bits 2))) else (if i.val < 30 then (if i.val < 29 then true else (true == bits 0)) else (if i.val < 31 then (true == bits 0) else true)))))
private def characters : BinaryRowCharacters C where
  values := values
  identity_eq := by decide +kernel
  parent_eq := by decide +kernel

private def conjugator7 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,1,2,3,4,5,6,7] : Array (Fin 8))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def forward7 (i : Fin 32) : Fin 32 :=
  (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 1) else (if i.val < 3 then 2 else 3)) else (if i.val < 6 then (if i.val < 5 then 4 else 5) else (if i.val < 7 then 6 else 7))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 8 else 9) else (if i.val < 11 then 10 else 11)) else (if i.val < 14 then (if i.val < 13 then 12 else 13) else (if i.val < 15 then 14 else 15)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 16 else 17) else (if i.val < 19 then 18 else 19)) else (if i.val < 22 then (if i.val < 21 then 20 else 21) else (if i.val < 23 then 22 else 23))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 24 else 25) else (if i.val < 27 then 26 else 27)) else (if i.val < 30 then (if i.val < 29 then 28 else 29) else (if i.val < 31 then 30 else 31)))))
private def backward7 (j : Fin 32) : Fin 32 :=
  (if j.val < 16 then (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 0 else 1) else (if j.val < 3 then 2 else 3)) else (if j.val < 6 then (if j.val < 5 then 4 else 5) else (if j.val < 7 then 6 else 7))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then 8 else 9) else (if j.val < 11 then 10 else 11)) else (if j.val < 14 then (if j.val < 13 then 12 else 13) else (if j.val < 15 then 14 else 15)))) else (if j.val < 24 then (if j.val < 20 then (if j.val < 18 then (if j.val < 17 then 16 else 17) else (if j.val < 19 then 18 else 19)) else (if j.val < 22 then (if j.val < 21 then 20 else 21) else (if j.val < 23 then 22 else 23))) else (if j.val < 28 then (if j.val < 26 then (if j.val < 25 then 24 else 25) else (if j.val < 27 then 26 else 27)) else (if j.val < 30 then (if j.val < 29 then 28 else 29) else (if j.val < 31 then 30 else 31)))))
private theorem forward_checked7 : ∀ i,
    characters.values (binaryAssignment (7 : Fin 8)) i = true →
    registry.rows 17 (forward7 i) = permutationConjugateCode conjugator7 (C.rows i) :=
  (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))
private theorem backward_checked7 : ∀ j,
    characters.values (binaryAssignment (7 : Fin 8)) (backward7 j) = true ∧
    registry.rows 17 j = permutationConjugateCode conjugator7 (C.rows (backward7 j)) :=
  (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))

private theorem checked : ∀ bits : Fin 3 → Bool,
    (∀ i j, characters.values bits (C.next i j) = (characters.values bits i == bits j)) →
    (∀ y : Fin 8, ∃ i, characters.values bits i = true ∧ encodedRowAction C i 0 = y) →
    ∃ k, ∃ g : Equiv.Perm (Fin 8),
      (∀ i, characters.values bits i = true →
        ∃ j, registry.rows k j = permutationConjugateCode g (C.rows i)) ∧
      (∀ j, ∃ i, characters.values bits i = true ∧
        registry.rows k j = permutationConjugateCode g (C.rows i)) := by
  intro bits
  obtain ⟨b,rfl⟩ := binaryAssignment_surjective 3 bits
  fin_cases b
  · intro hs _
    exact False.elim ((show ¬(∀ i j, characters.values (binaryAssignment (0 : Fin 8))
      (C.next i j) = (characters.values (binaryAssignment (0 : Fin 8)) i ==
        binaryAssignment (0 : Fin 8) j)) from by decide +kernel) hs)
  · intro _ ht
    exact False.elim ((show ¬(∀ y : Fin 8, ∃ i,
      characters.values (binaryAssignment (1 : Fin 8)) i = true ∧
        encodedRowAction C i 0 = y) from by decide +kernel) ht)
  · intro hs _
    exact False.elim ((show ¬(∀ i j, characters.values (binaryAssignment (2 : Fin 8))
      (C.next i j) = (characters.values (binaryAssignment (2 : Fin 8)) i ==
        binaryAssignment (2 : Fin 8) j)) from by decide +kernel) hs)
  · intro _ ht
    exact False.elim ((show ¬(∀ y : Fin 8, ∃ i,
      characters.values (binaryAssignment (3 : Fin 8)) i = true ∧
        encodedRowAction C i 0 = y) from by decide +kernel) ht)
  · intro hs _
    exact False.elim ((show ¬(∀ i j, characters.values (binaryAssignment (4 : Fin 8))
      (C.next i j) = (characters.values (binaryAssignment (4 : Fin 8)) i ==
        binaryAssignment (4 : Fin 8) j)) from by decide +kernel) hs)
  · intro _ ht
    exact False.elim ((show ¬(∀ y : Fin 8, ∃ i,
      characters.values (binaryAssignment (5 : Fin 8)) i = true ∧
        encodedRowAction C i 0 = y) from by decide +kernel) ht)
  · intro hs _
    exact False.elim ((show ¬(∀ i j, characters.values (binaryAssignment (6 : Fin 8))
      (C.next i j) = (characters.values (binaryAssignment (6 : Fin 8)) i ==
        binaryAssignment (6 : Fin 8) j)) from by decide +kernel) hs)
  · intro _ _
    exact ⟨17,conjugator7,
      fun i hi => ⟨forward7 i,forward_checked7 i hi⟩,
      fun j => ⟨backward7 j,backward_checked7 j⟩⟩

/-- Complete literal transitive index-two child coverage for this original action. -/
theorem children (K : Subgroup (Equiv.Perm (Fin 8)))
    (hle : K ≤ Subgroup.closure (Set.range BinaryMenuCayley8T21.generators))
    (hindex : K.relIndex (Subgroup.closure (Set.range BinaryMenuCayley8T21.generators)) = 2)
    (ht : PermutationSubgroupTransitive K) : ActionRegistryCovered actions K :=
  binary_character_registry_children C characters actions registry 0 checked K hle hindex ht

end SymmetricSubgroupAsymptotics.BinaryActionChildren8T21
