import SymmetricSubgroupAsymptotics.BinaryActionRegistry8

/-! All original index-two transitive children of b8_5, checked by generator bits. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryActionChildren8T5
open BinaryActionRegistry8
private def C := BinaryMenuCayley8T5.certificate
private def values (bits : Fin 2 → Bool) (i : Fin 8) : Bool :=
  (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then (true == bits 0) else true) else (if i.val < 3 then (true == bits 0) else (true == bits 1))) else (if i.val < 6 then (if i.val < 5 then ((true == bits 0) == bits 1) else (true == bits 1)) else (if i.val < 7 then ((true == bits 0) == bits 1) else true)))
private def characters : BinaryRowCharacters C where
  values := values
  identity_eq := by decide +kernel
  parent_eq := by decide +kernel

private def conjugator3 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,1,2,3,4,5,6,7] : Array (Fin 8))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def forward3 (i : Fin 8) : Fin 8 :=
  (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 1) else (if i.val < 3 then 2 else 3)) else (if i.val < 6 then (if i.val < 5 then 4 else 5) else (if i.val < 7 then 6 else 7)))
private def backward3 (j : Fin 8) : Fin 8 :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 0 else 1) else (if j.val < 3 then 2 else 3)) else (if j.val < 6 then (if j.val < 5 then 4 else 5) else (if j.val < 7 then 6 else 7)))
private theorem forward_checked3 : ∀ i,
    characters.values (binaryAssignment (3 : Fin 4)) i = true →
    registry.rows 4 (forward3 i) = permutationConjugateCode conjugator3 (C.rows i) :=
  (by decide +kernel)
private theorem backward_checked3 : ∀ j,
    characters.values (binaryAssignment (3 : Fin 4)) (backward3 j) = true ∧
    registry.rows 4 j = permutationConjugateCode conjugator3 (C.rows (backward3 j)) :=
  (by decide +kernel)

private theorem checked : ∀ bits : Fin 2 → Bool,
    (∀ i j, characters.values bits (C.next i j) = (characters.values bits i == bits j)) →
    (∀ y : Fin 8, ∃ i, characters.values bits i = true ∧ encodedRowAction C i 0 = y) →
    ∃ k, ∃ g : Equiv.Perm (Fin 8),
      (∀ i, characters.values bits i = true →
        ∃ j, registry.rows k j = permutationConjugateCode g (C.rows i)) ∧
      (∀ j, ∃ i, characters.values bits i = true ∧
        registry.rows k j = permutationConjugateCode g (C.rows i)) := by
  intro bits
  obtain ⟨b,rfl⟩ := binaryAssignment_surjective 2 bits
  fin_cases b
  · intro _ ht
    exact False.elim ((show ¬(∀ y : Fin 8, ∃ i,
      characters.values (binaryAssignment (0 : Fin 4)) i = true ∧
        encodedRowAction C i 0 = y) from by decide +kernel) ht)
  · intro _ ht
    exact False.elim ((show ¬(∀ y : Fin 8, ∃ i,
      characters.values (binaryAssignment (1 : Fin 4)) i = true ∧
        encodedRowAction C i 0 = y) from by decide +kernel) ht)
  · intro _ ht
    exact False.elim ((show ¬(∀ y : Fin 8, ∃ i,
      characters.values (binaryAssignment (2 : Fin 4)) i = true ∧
        encodedRowAction C i 0 = y) from by decide +kernel) ht)
  · intro _ _
    exact ⟨4,conjugator3,
      fun i hi => ⟨forward3 i,forward_checked3 i hi⟩,
      fun j => ⟨backward3 j,backward_checked3 j⟩⟩

/-- Complete literal transitive index-two child coverage for this original action. -/
theorem children (K : Subgroup (Equiv.Perm (Fin 8)))
    (hle : K ≤ Subgroup.closure (Set.range BinaryMenuCayley8T5.generators))
    (hindex : K.relIndex (Subgroup.closure (Set.range BinaryMenuCayley8T5.generators)) = 2)
    (ht : PermutationSubgroupTransitive K) : ActionRegistryCovered actions K :=
  binary_character_registry_children C characters actions registry 0 checked K hle hindex ht

end SymmetricSubgroupAsymptotics.BinaryActionChildren8T5
