import SymmetricSubgroupAsymptotics.BinaryActionRegistry8

/-! All original index-two transitive children of b8_9, checked by generator bits. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryActionChildren8T9
open BinaryActionRegistry8
private def C := BinaryMenuCayley8T9.certificate
private def values (bits : Fin 4 → Bool) (i : Fin 16) : Bool :=
  (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then (true == bits 0) else ((true == bits 0) == bits 3)) else (if i.val < 3 then ((true == bits 1) == bits 3) else (true == bits 1))) else (if i.val < 6 then (if i.val < 5 then ((true == bits 0) == bits 1) else (((true == bits 0) == bits 1) == bits 3)) else (if i.val < 7 then ((true == bits 2) == bits 3) else (true == bits 2)))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then ((true == bits 0) == bits 2) else ((true == bits 2) == bits 3)) else (if i.val < 11 then ((true == bits 1) == bits 2) else (((true == bits 1) == bits 2) == bits 3))) else (if i.val < 14 then (if i.val < 13 then (((true == bits 1) == bits 2) == bits 3) else (((true == bits 0) == bits 1) == bits 2)) else (if i.val < 15 then (true == bits 3) else true))))
private def characters : BinaryRowCharacters C where
  values := values
  identity_eq := by decide +kernel
  parent_eq := by decide +kernel

private def conjugator1 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,5,3,7,1,6,4,2] : Array (Fin 8))[x.val]!
  invFun x := (#[0,4,7,2,6,1,5,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def forward1 (i : Fin 16) : Fin 8 :=
  (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 1 else 0) else (if i.val < 3 then 4 else 0)) else (if i.val < 6 then (if i.val < 5 then 0 else 6) else (if i.val < 7 then 0 else 0))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 0 else 2) else (if i.val < 11 then 5 else 0)) else (if i.val < 14 then (if i.val < 13 then 0 else 3) else (if i.val < 15 then 0 else 7))))
private def backward1 (j : Fin 8) : Fin 16 :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 6 else 0) else (if j.val < 3 then 9 else 13)) else (if j.val < 6 then (if j.val < 5 then 2 else 10) else (if j.val < 7 then 5 else 15)))
private theorem forward_checked1 : ∀ i,
    characters.values (binaryAssignment (1 : Fin 16)) i = true →
    registry.rows 3 (forward1 i) = permutationConjugateCode conjugator1 (C.rows i) :=
  (by decide +kernel)
private theorem backward_checked1 : ∀ j,
    characters.values (binaryAssignment (1 : Fin 16)) (backward1 j) = true ∧
    registry.rows 3 j = permutationConjugateCode conjugator1 (C.rows (backward1 j)) :=
  (by decide +kernel)

private def conjugator3 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,6,4,1,7,5,3,2] : Array (Fin 8))[x.val]!
  invFun x := (#[0,3,7,6,2,5,1,4] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def forward3 (i : Fin 16) : Fin 8 :=
  (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 1 else 0) else (if i.val < 3 then 0 else 3)) else (if i.val < 6 then (if i.val < 5 then 5 else 0) else (if i.val < 7 then 2 else 0))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 0 else 0) else (if i.val < 11 then 0 else 6)) else (if i.val < 14 then (if i.val < 13 then 4 else 0) else (if i.val < 15 then 0 else 7))))
private def backward3 (j : Fin 8) : Fin 16 :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 9 else 0) else (if j.val < 3 then 6 else 3)) else (if j.val < 6 then (if j.val < 5 then 12 else 4) else (if j.val < 7 then 11 else 15)))
private theorem forward_checked3 : ∀ i,
    characters.values (binaryAssignment (3 : Fin 16)) i = true →
    registry.rows 1 (forward3 i) = permutationConjugateCode conjugator3 (C.rows i) :=
  (by decide +kernel)
private theorem backward_checked3 : ∀ j,
    characters.values (binaryAssignment (3 : Fin 16)) (backward3 j) = true ∧
    registry.rows 1 j = permutationConjugateCode conjugator3 (C.rows (backward3 j)) :=
  (by decide +kernel)

private def conjugator5 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,5,3,6,4,7,1,2] : Array (Fin 8))[x.val]!
  invFun x := (#[0,6,7,2,4,1,3,5] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def forward5 (i : Fin 16) : Fin 8 :=
  (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 1 else 0) else (if i.val < 3 then 4 else 0)) else (if i.val < 6 then (if i.val < 5 then 0 else 6) else (if i.val < 7 then 0 else 5))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 3 else 0) else (if i.val < 11 then 0 else 0)) else (if i.val < 14 then (if i.val < 13 then 2 else 0) else (if i.val < 15 then 0 else 7))))
private def backward5 (j : Fin 8) : Fin 16 :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 11 else 0) else (if j.val < 3 then 12 else 8)) else (if j.val < 6 then (if j.val < 5 then 2 else 7) else (if j.val < 7 then 5 else 15)))
private theorem forward_checked5 : ∀ i,
    characters.values (binaryAssignment (5 : Fin 16)) i = true →
    registry.rows 3 (forward5 i) = permutationConjugateCode conjugator5 (C.rows i) :=
  (by decide +kernel)
private theorem backward_checked5 : ∀ j,
    characters.values (binaryAssignment (5 : Fin 16)) (backward5 j) = true ∧
    registry.rows 3 j = permutationConjugateCode conjugator5 (C.rows (backward5 j)) :=
  (by decide +kernel)

private def conjugator7 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,1,2,3,4,5,6,7] : Array (Fin 8))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def forward7 (i : Fin 16) : Fin 8 :=
  (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 1)) else (if i.val < 6 then (if i.val < 5 then 2 else 0) else (if i.val < 7 then 0 else 3))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 4 else 0) else (if i.val < 11 then 5 else 0)) else (if i.val < 14 then (if i.val < 13 then 0 else 6) else (if i.val < 15 then 0 else 7))))
private def backward7 (j : Fin 8) : Fin 16 :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 0 else 3) else (if j.val < 3 then 4 else 7)) else (if j.val < 6 then (if j.val < 5 then 8 else 10) else (if j.val < 7 then 13 else 15)))
private theorem forward_checked7 : ∀ i,
    characters.values (binaryAssignment (7 : Fin 16)) i = true →
    registry.rows 2 (forward7 i) = permutationConjugateCode conjugator7 (C.rows i) :=
  (by decide +kernel)
private theorem backward_checked7 : ∀ j,
    characters.values (binaryAssignment (7 : Fin 16)) (backward7 j) = true ∧
    registry.rows 2 j = permutationConjugateCode conjugator7 (C.rows (backward7 j)) :=
  (by decide +kernel)

private def conjugator15 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,1,2,3,4,5,6,7] : Array (Fin 8))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def forward15 (i : Fin 16) : Fin 16 :=
  (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 1) else (if i.val < 3 then 2 else 3)) else (if i.val < 6 then (if i.val < 5 then 4 else 5) else (if i.val < 7 then 6 else 7))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 8 else 9) else (if i.val < 11 then 10 else 11)) else (if i.val < 14 then (if i.val < 13 then 12 else 13) else (if i.val < 15 then 14 else 15))))
private def backward15 (j : Fin 16) : Fin 16 :=
  (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 0 else 1) else (if j.val < 3 then 2 else 3)) else (if j.val < 6 then (if j.val < 5 then 4 else 5) else (if j.val < 7 then 6 else 7))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then 8 else 9) else (if j.val < 11 then 10 else 11)) else (if j.val < 14 then (if j.val < 13 then 12 else 13) else (if j.val < 15 then 14 else 15))))
private theorem forward_checked15 : ∀ i,
    characters.values (binaryAssignment (15 : Fin 16)) i = true →
    registry.rows 8 (forward15 i) = permutationConjugateCode conjugator15 (C.rows i) :=
  (by decide +kernel)
private theorem backward_checked15 : ∀ j,
    characters.values (binaryAssignment (15 : Fin 16)) (backward15 j) = true ∧
    registry.rows 8 j = permutationConjugateCode conjugator15 (C.rows (backward15 j)) :=
  (by decide +kernel)

private theorem checked : ∀ bits : Fin 4 → Bool,
    (∀ i j, characters.values bits (C.next i j) = (characters.values bits i == bits j)) →
    (∀ y : Fin 8, ∃ i, characters.values bits i = true ∧ encodedRowAction C i 0 = y) →
    ∃ k, ∃ g : Equiv.Perm (Fin 8),
      (∀ i, characters.values bits i = true →
        ∃ j, registry.rows k j = permutationConjugateCode g (C.rows i)) ∧
      (∀ j, ∃ i, characters.values bits i = true ∧
        registry.rows k j = permutationConjugateCode g (C.rows i)) := by
  intro bits
  obtain ⟨b,rfl⟩ := binaryAssignment_surjective 4 bits
  fin_cases b
  · intro hs _
    exact False.elim ((show ¬(∀ i j, characters.values (binaryAssignment (0 : Fin 16))
      (C.next i j) = (characters.values (binaryAssignment (0 : Fin 16)) i ==
        binaryAssignment (0 : Fin 16) j)) from by decide +kernel) hs)
  · intro _ _
    exact ⟨3,conjugator1,
      fun i hi => ⟨forward1 i,forward_checked1 i hi⟩,
      fun j => ⟨backward1 j,backward_checked1 j⟩⟩
  · intro hs _
    exact False.elim ((show ¬(∀ i j, characters.values (binaryAssignment (2 : Fin 16))
      (C.next i j) = (characters.values (binaryAssignment (2 : Fin 16)) i ==
        binaryAssignment (2 : Fin 16) j)) from by decide +kernel) hs)
  · intro _ _
    exact ⟨1,conjugator3,
      fun i hi => ⟨forward3 i,forward_checked3 i hi⟩,
      fun j => ⟨backward3 j,backward_checked3 j⟩⟩
  · intro hs _
    exact False.elim ((show ¬(∀ i j, characters.values (binaryAssignment (4 : Fin 16))
      (C.next i j) = (characters.values (binaryAssignment (4 : Fin 16)) i ==
        binaryAssignment (4 : Fin 16) j)) from by decide +kernel) hs)
  · intro _ _
    exact ⟨3,conjugator5,
      fun i hi => ⟨forward5 i,forward_checked5 i hi⟩,
      fun j => ⟨backward5 j,backward_checked5 j⟩⟩
  · intro hs _
    exact False.elim ((show ¬(∀ i j, characters.values (binaryAssignment (6 : Fin 16))
      (C.next i j) = (characters.values (binaryAssignment (6 : Fin 16)) i ==
        binaryAssignment (6 : Fin 16) j)) from by decide +kernel) hs)
  · intro _ _
    exact ⟨2,conjugator7,
      fun i hi => ⟨forward7 i,forward_checked7 i hi⟩,
      fun j => ⟨backward7 j,backward_checked7 j⟩⟩
  · intro hs _
    exact False.elim ((show ¬(∀ i j, characters.values (binaryAssignment (8 : Fin 16))
      (C.next i j) = (characters.values (binaryAssignment (8 : Fin 16)) i ==
        binaryAssignment (8 : Fin 16) j)) from by decide +kernel) hs)
  · intro _ ht
    exact False.elim ((show ¬(∀ y : Fin 8, ∃ i,
      characters.values (binaryAssignment (9 : Fin 16)) i = true ∧
        encodedRowAction C i 0 = y) from by decide +kernel) ht)
  · intro hs _
    exact False.elim ((show ¬(∀ i j, characters.values (binaryAssignment (10 : Fin 16))
      (C.next i j) = (characters.values (binaryAssignment (10 : Fin 16)) i ==
        binaryAssignment (10 : Fin 16) j)) from by decide +kernel) hs)
  · intro _ ht
    exact False.elim ((show ¬(∀ y : Fin 8, ∃ i,
      characters.values (binaryAssignment (11 : Fin 16)) i = true ∧
        encodedRowAction C i 0 = y) from by decide +kernel) ht)
  · intro hs _
    exact False.elim ((show ¬(∀ i j, characters.values (binaryAssignment (12 : Fin 16))
      (C.next i j) = (characters.values (binaryAssignment (12 : Fin 16)) i ==
        binaryAssignment (12 : Fin 16) j)) from by decide +kernel) hs)
  · intro _ ht
    exact False.elim ((show ¬(∀ y : Fin 8, ∃ i,
      characters.values (binaryAssignment (13 : Fin 16)) i = true ∧
        encodedRowAction C i 0 = y) from by decide +kernel) ht)
  · intro hs _
    exact False.elim ((show ¬(∀ i j, characters.values (binaryAssignment (14 : Fin 16))
      (C.next i j) = (characters.values (binaryAssignment (14 : Fin 16)) i ==
        binaryAssignment (14 : Fin 16) j)) from by decide +kernel) hs)
  · intro _ _
    exact ⟨8,conjugator15,
      fun i hi => ⟨forward15 i,forward_checked15 i hi⟩,
      fun j => ⟨backward15 j,backward_checked15 j⟩⟩

/-- Complete literal transitive index-two child coverage for this original action. -/
theorem children (K : Subgroup (Equiv.Perm (Fin 8)))
    (hle : K ≤ Subgroup.closure (Set.range BinaryMenuCayley8T9.generators))
    (hindex : K.relIndex (Subgroup.closure (Set.range BinaryMenuCayley8T9.generators)) = 2)
    (ht : PermutationSubgroupTransitive K) : ActionRegistryCovered actions K :=
  binary_character_registry_children C characters actions registry 0 checked K hle hindex ht

end SymmetricSubgroupAsymptotics.BinaryActionChildren8T9
