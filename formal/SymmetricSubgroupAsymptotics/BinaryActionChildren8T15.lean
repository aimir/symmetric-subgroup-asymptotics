import SymmetricSubgroupAsymptotics.BinaryActionRegistry8

/-! All original index-two transitive children of b8_15, checked by generator bits. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryActionChildren8T15
open BinaryActionRegistry8
private def C := BinaryMenuCayley8T15.certificate
private def values (bits : Fin 3 → Bool) (i : Fin 32) : Bool :=
  (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then (true == bits 2) else ((true == bits 0) == bits 1)) else (if i.val < 3 then ((true == bits 1) == bits 2) else (true == bits 0))) else (if i.val < 6 then (if i.val < 5 then true else ((true == bits 0) == bits 2)) else (if i.val < 7 then (true == bits 1) else (((true == bits 0) == bits 1) == bits 2)))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then (true == bits 0) else (true == bits 2)) else (if i.val < 11 then ((true == bits 0) == bits 1) else ((true == bits 1) == bits 2))) else (if i.val < 14 then (if i.val < 13 then (((true == bits 0) == bits 1) == bits 2) else true) else (if i.val < 15 then ((true == bits 0) == bits 2) else (true == bits 1))))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then ((true == bits 1) == bits 2) else (true == bits 0)) else (if i.val < 19 then (true == bits 2) else ((true == bits 0) == bits 1))) else (if i.val < 22 then (if i.val < 21 then (true == bits 1) else (((true == bits 0) == bits 1) == bits 2)) else (if i.val < 23 then true else ((true == bits 0) == bits 2)))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then ((true == bits 0) == bits 1) else ((true == bits 1) == bits 2)) else (if i.val < 27 then (true == bits 0) else (true == bits 2))) else (if i.val < 30 then (if i.val < 29 then ((true == bits 0) == bits 2) else (true == bits 1)) else (if i.val < 31 then (((true == bits 0) == bits 1) == bits 2) else true)))))
private def characters : BinaryRowCharacters C where
  values := values
  identity_eq := by decide +kernel
  parent_eq := by decide +kernel

private def conjugator0 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,5,6,3,4,1,2,7] : Array (Fin 8))[x.val]!
  invFun x := (#[0,5,6,3,4,1,2,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def forward0 (i : Fin 32) : Fin 16 :=
  (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 1) else (if i.val < 3 then 0 else 0)) else (if i.val < 6 then (if i.val < 5 then 11 else 10) else (if i.val < 7 then 0 else 0))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 0 else 0) else (if i.val < 11 then 13 else 12)) else (if i.val < 14 then (if i.val < 13 then 0 else 7) else (if i.val < 15 then 6 else 0)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 8 else 0) else (if i.val < 19 then 0 else 9)) else (if i.val < 22 then (if i.val < 21 then 0 else 0) else (if i.val < 23 then 2 else 3))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 4 else 5) else (if i.val < 27 then 0 else 0)) else (if i.val < 30 then (if i.val < 29 then 14 else 0) else (if i.val < 31 then 0 else 15)))))
private def backward0 (j : Fin 16) : Fin 32 :=
  (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 2 else 1) else (if j.val < 3 then 22 else 23)) else (if j.val < 6 then (if j.val < 5 then 24 else 25) else (if j.val < 7 then 14 else 13))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then 16 else 19) else (if j.val < 11 then 5 else 4)) else (if j.val < 14 then (if j.val < 13 then 11 else 10) else (if j.val < 15 then 28 else 31))))
private theorem forward_checked0 : ∀ i,
    characters.values (binaryAssignment (0 : Fin 8)) i = true →
    registry.rows 7 (forward0 i) = permutationConjugateCode conjugator0 (C.rows i) :=
  (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))
private theorem backward_checked0 : ∀ j,
    characters.values (binaryAssignment (0 : Fin 8)) (backward0 j) = true ∧
    registry.rows 7 j = permutationConjugateCode conjugator0 (C.rows (backward0 j)) :=
  (by decide +kernel)

private def conjugator1 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,1,2,3,4,5,6,7] : Array (Fin 8))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def forward1 (i : Fin 32) : Fin 16 :=
  (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 1)) else (if i.val < 6 then (if i.val < 5 then 2 else 0) else (if i.val < 7 then 0 else 3))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 4 else 0) else (if i.val < 11 then 0 else 5)) else (if i.val < 14 then (if i.val < 13 then 6 else 7) else (if i.val < 15 then 0 else 0)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 8 else 9) else (if i.val < 19 then 0 else 0)) else (if i.val < 22 then (if i.val < 21 then 0 else 10) else (if i.val < 23 then 11 else 0))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 0 else 12) else (if i.val < 27 then 13 else 0)) else (if i.val < 30 then (if i.val < 29 then 0 else 0) else (if i.val < 31 then 14 else 15)))))
private def backward1 (j : Fin 16) : Fin 32 :=
  (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 2 else 3) else (if j.val < 3 then 4 else 7)) else (if j.val < 6 then (if j.val < 5 then 8 else 11) else (if j.val < 7 then 12 else 13))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then 16 else 17) else (if j.val < 11 then 21 else 22)) else (if j.val < 14 then (if j.val < 13 then 25 else 26) else (if j.val < 15 then 30 else 31))))
private theorem forward_checked1 : ∀ i,
    characters.values (binaryAssignment (1 : Fin 8)) i = true →
    registry.rows 7 (forward1 i) = permutationConjugateCode conjugator1 (C.rows i) :=
  (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))
private theorem backward_checked1 : ∀ j,
    characters.values (binaryAssignment (1 : Fin 8)) (backward1 j) = true ∧
    registry.rows 7 j = permutationConjugateCode conjugator1 (C.rows (backward1 j)) :=
  (by decide +kernel)

private def conjugator3 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,1,2,3,4,5,6,7] : Array (Fin 8))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def forward3 (i : Fin 32) : Fin 16 :=
  (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 1)) else (if i.val < 6 then (if i.val < 5 then 2 else 0) else (if i.val < 7 then 3 else 0))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 4 else 0) else (if i.val < 11 then 5 else 0)) else (if i.val < 14 then (if i.val < 13 then 0 else 6) else (if i.val < 15 then 0 else 7)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 0 else 8) else (if i.val < 19 then 0 else 9)) else (if i.val < 22 then (if i.val < 21 then 10 else 0) else (if i.val < 23 then 11 else 0))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 12 else 0) else (if i.val < 27 then 13 else 0)) else (if i.val < 30 then (if i.val < 29 then 0 else 14) else (if i.val < 31 then 0 else 15)))))
private def backward3 (j : Fin 16) : Fin 32 :=
  (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 1 else 3) else (if j.val < 3 then 4 else 6)) else (if j.val < 6 then (if j.val < 5 then 8 else 10) else (if j.val < 7 then 13 else 15))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then 17 else 19) else (if j.val < 11 then 20 else 22)) else (if j.val < 14 then (if j.val < 13 then 24 else 26) else (if j.val < 15 then 29 else 31))))
private theorem forward_checked3 : ∀ i,
    characters.values (binaryAssignment (3 : Fin 8)) i = true →
    registry.rows 6 (forward3 i) = permutationConjugateCode conjugator3 (C.rows i) :=
  (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))
private theorem backward_checked3 : ∀ j,
    characters.values (binaryAssignment (3 : Fin 8)) (backward3 j) = true ∧
    registry.rows 6 j = permutationConjugateCode conjugator3 (C.rows (backward3 j)) :=
  (by decide +kernel)

private def conjugator4 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,5,6,3,4,1,2,7] : Array (Fin 8))[x.val]!
  invFun x := (#[0,5,6,3,4,1,2,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def forward4 (i : Fin 32) : Fin 16 :=
  (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 1) else (if i.val < 3 then 0 else 0)) else (if i.val < 6 then (if i.val < 5 then 10 else 0) else (if i.val < 7 then 0 else 11))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 0 else 13) else (if i.val < 11 then 12 else 0)) else (if i.val < 14 then (if i.val < 13 then 7 else 6) else (if i.val < 15 then 0 else 0)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 0 else 0) else (if i.val < 19 then 9 else 8)) else (if i.val < 22 then (if i.val < 21 then 0 else 3) else (if i.val < 23 then 2 else 0))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 4 else 0) else (if i.val < 27 then 0 else 5)) else (if i.val < 30 then (if i.val < 29 then 0 else 0) else (if i.val < 31 then 14 else 15)))))
private def backward4 (j : Fin 16) : Fin 32 :=
  (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 0 else 1) else (if j.val < 3 then 22 else 21)) else (if j.val < 6 then (if j.val < 5 then 24 else 27) else (if j.val < 7 then 13 else 12))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then 19 else 18) else (if j.val < 11 then 4 else 7)) else (if j.val < 14 then (if j.val < 13 then 10 else 9) else (if j.val < 15 then 30 else 31))))
private theorem forward_checked4 : ∀ i,
    characters.values (binaryAssignment (4 : Fin 8)) i = true →
    registry.rows 5 (forward4 i) = permutationConjugateCode conjugator4 (C.rows i) :=
  (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))
private theorem backward_checked4 : ∀ j,
    characters.values (binaryAssignment (4 : Fin 8)) (backward4 j) = true ∧
    registry.rows 5 j = permutationConjugateCode conjugator4 (C.rows (backward4 j)) :=
  (by decide +kernel)

private def conjugator5 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,1,2,3,4,5,6,7] : Array (Fin 8))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def forward5 (i : Fin 32) : Fin 16 :=
  (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 1)) else (if i.val < 6 then (if i.val < 5 then 2 else 3) else (if i.val < 7 then 0 else 0))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 4 else 5) else (if i.val < 11 then 0 else 0)) else (if i.val < 14 then (if i.val < 13 then 0 else 6) else (if i.val < 15 then 7 else 0)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 0 else 8) else (if i.val < 19 then 9 else 0)) else (if i.val < 22 then (if i.val < 21 then 0 else 0) else (if i.val < 23 then 10 else 11))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 0 else 0) else (if i.val < 27 then 12 else 13)) else (if i.val < 30 then (if i.val < 29 then 14 else 0) else (if i.val < 31 then 0 else 15)))))
private def backward5 (j : Fin 16) : Fin 32 :=
  (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 0 else 3) else (if j.val < 3 then 4 else 5)) else (if j.val < 6 then (if j.val < 5 then 8 else 9) else (if j.val < 7 then 13 else 14))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then 17 else 18) else (if j.val < 11 then 22 else 23)) else (if j.val < 14 then (if j.val < 13 then 26 else 27) else (if j.val < 15 then 28 else 31))))
private theorem forward_checked5 : ∀ i,
    characters.values (binaryAssignment (5 : Fin 8)) i = true →
    registry.rows 5 (forward5 i) = permutationConjugateCode conjugator5 (C.rows i) :=
  (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))
private theorem backward_checked5 : ∀ j,
    characters.values (binaryAssignment (5 : Fin 8)) (backward5 j) = true ∧
    registry.rows 5 j = permutationConjugateCode conjugator5 (C.rows (backward5 j)) :=
  (by decide +kernel)

private def conjugator6 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,5,2,3,4,1,6,7] : Array (Fin 8))[x.val]!
  invFun x := (#[0,5,2,3,4,1,6,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def forward6 (i : Fin 32) : Fin 16 :=
  (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 1 else 0) else (if i.val < 3 then 0 else 0)) else (if i.val < 6 then (if i.val < 5 then 10 else 0) else (if i.val < 7 then 11 else 0))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 0 else 4) else (if i.val < 11 then 0 else 5)) else (if i.val < 14 then (if i.val < 13 then 0 else 6) else (if i.val < 15 then 0 else 7)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 9 else 0) else (if i.val < 19 then 8 else 0)) else (if i.val < 22 then (if i.val < 21 then 2 else 0) else (if i.val < 23 then 3 else 0))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 0 else 12) else (if i.val < 27 then 0 else 13)) else (if i.val < 30 then (if i.val < 29 then 0 else 14) else (if i.val < 31 then 0 else 15)))))
private def backward6 (j : Fin 16) : Fin 32 :=
  (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 2 else 0) else (if j.val < 3 then 20 else 22)) else (if j.val < 6 then (if j.val < 5 then 9 else 11) else (if j.val < 7 then 13 else 15))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then 18 else 16) else (if j.val < 11 then 4 else 6)) else (if j.val < 14 then (if j.val < 13 then 25 else 27) else (if j.val < 15 then 29 else 31))))
private theorem forward_checked6 : ∀ i,
    characters.values (binaryAssignment (6 : Fin 8)) i = true →
    registry.rows 10 (forward6 i) = permutationConjugateCode conjugator6 (C.rows i) :=
  (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))
private theorem backward_checked6 : ∀ j,
    characters.values (binaryAssignment (6 : Fin 8)) (backward6 j) = true ∧
    registry.rows 10 j = permutationConjugateCode conjugator6 (C.rows (backward6 j)) :=
  (by decide +kernel)

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
    registry.rows 11 (forward7 i) = permutationConjugateCode conjugator7 (C.rows i) :=
  (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))
private theorem backward_checked7 : ∀ j,
    characters.values (binaryAssignment (7 : Fin 8)) (backward7 j) = true ∧
    registry.rows 11 j = permutationConjugateCode conjugator7 (C.rows (backward7 j)) :=
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
  · intro _ _
    exact ⟨7,conjugator0,
      fun i hi => ⟨forward0 i,forward_checked0 i hi⟩,
      fun j => ⟨backward0 j,backward_checked0 j⟩⟩
  · intro _ _
    exact ⟨7,conjugator1,
      fun i hi => ⟨forward1 i,forward_checked1 i hi⟩,
      fun j => ⟨backward1 j,backward_checked1 j⟩⟩
  · intro _ ht
    exact False.elim ((show ¬(∀ y : Fin 8, ∃ i,
      characters.values (binaryAssignment (2 : Fin 8)) i = true ∧
        encodedRowAction C i 0 = y) from by decide +kernel) ht)
  · intro _ _
    exact ⟨6,conjugator3,
      fun i hi => ⟨forward3 i,forward_checked3 i hi⟩,
      fun j => ⟨backward3 j,backward_checked3 j⟩⟩
  · intro _ _
    exact ⟨5,conjugator4,
      fun i hi => ⟨forward4 i,forward_checked4 i hi⟩,
      fun j => ⟨backward4 j,backward_checked4 j⟩⟩
  · intro _ _
    exact ⟨5,conjugator5,
      fun i hi => ⟨forward5 i,forward_checked5 i hi⟩,
      fun j => ⟨backward5 j,backward_checked5 j⟩⟩
  · intro _ _
    exact ⟨10,conjugator6,
      fun i hi => ⟨forward6 i,forward_checked6 i hi⟩,
      fun j => ⟨backward6 j,backward_checked6 j⟩⟩
  · intro _ _
    exact ⟨11,conjugator7,
      fun i hi => ⟨forward7 i,forward_checked7 i hi⟩,
      fun j => ⟨backward7 j,backward_checked7 j⟩⟩

/-- Complete literal transitive index-two child coverage for this original action. -/
theorem children (K : Subgroup (Equiv.Perm (Fin 8)))
    (hle : K ≤ Subgroup.closure (Set.range BinaryMenuCayley8T15.generators))
    (hindex : K.relIndex (Subgroup.closure (Set.range BinaryMenuCayley8T15.generators)) = 2)
    (ht : PermutationSubgroupTransitive K) : ActionRegistryCovered actions K :=
  binary_character_registry_children C characters actions registry 0 checked K hle hindex ht

end SymmetricSubgroupAsymptotics.BinaryActionChildren8T15
