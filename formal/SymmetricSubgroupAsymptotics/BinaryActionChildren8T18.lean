import SymmetricSubgroupAsymptotics.BinaryActionRegistry8

/-! All original index-two transitive children of b8_18, checked by generator bits. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryActionChildren8T18
open BinaryActionRegistry8
private def C := BinaryMenuCayley8T18.certificate
private def values (bits : Fin 5 → Bool) (i : Fin 32) : Bool :=
  (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then ((true == bits 0) == bits 4) else (((true == bits 0) == bits 3) == bits 4)) else (if i.val < 3 then (true == bits 0) else ((true == bits 0) == bits 3))) else (if i.val < 6 then (if i.val < 5 then ((true == bits 1) == bits 3) else (true == bits 1)) else (if i.val < 7 then (((true == bits 1) == bits 3) == bits 4) else ((true == bits 1) == bits 4)))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then ((true == bits 0) == bits 1) else (((true == bits 0) == bits 1) == bits 3)) else (if i.val < 11 then (((true == bits 0) == bits 1) == bits 4) else ((((true == bits 0) == bits 1) == bits 3) == bits 4))) else (if i.val < 14 then (if i.val < 13 then ((true == bits 2) == bits 4) else ((true == bits 2) == bits 3)) else (if i.val < 15 then (true == bits 2) else (((true == bits 2) == bits 3) == bits 4))))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then (((true == bits 2) == bits 3) == bits 4) else ((true == bits 0) == bits 2)) else (if i.val < 19 then ((true == bits 2) == bits 3) else (((true == bits 0) == bits 2) == bits 4))) else (if i.val < 22 then (if i.val < 21 then ((true == bits 1) == bits 2) else (((true == bits 2) == bits 3) == bits 4)) else (if i.val < 23 then ((true == bits 2) == bits 4) else (((true == bits 1) == bits 2) == bits 3)))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then (((true == bits 1) == bits 2) == bits 3) else (((true == bits 0) == bits 2) == bits 4)) else (if i.val < 27 then (((true == bits 2) == bits 3) == bits 4) else (((true == bits 0) == bits 1) == bits 2))) else (if i.val < 30 then (if i.val < 29 then ((true == bits 3) == bits 4) else (true == bits 4)) else (if i.val < 31 then (true == bits 3) else true)))))
private def characters : BinaryRowCharacters C where
  values := values
  identity_eq := by decide +kernel
  parent_eq := by decide +kernel

private def conjugator3 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,4,2,7,5,1,3,6] : Array (Fin 8))[x.val]!
  invFun x := (#[0,5,2,6,1,4,7,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def forward3 (i : Fin 32) : Fin 16 :=
  (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 2) else (if i.val < 3 then 10 else 0)) else (if i.val < 6 then (if i.val < 5 then 0 else 3) else (if i.val < 7 then 11 else 0))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 6 else 0) else (if i.val < 11 then 0 else 14)) else (if i.val < 14 then (if i.val < 13 then 9 else 1) else (if i.val < 15 then 0 else 0)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 0 else 0) else (if i.val < 19 then 13 else 5)) else (if i.val < 22 then (if i.val < 21 then 0 else 0) else (if i.val < 23 then 12 else 4))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 8 else 0) else (if i.val < 27 then 0 else 0)) else (if i.val < 30 then (if i.val < 29 then 7 else 0) else (if i.val < 31 then 0 else 15)))))
private def backward3 (j : Fin 16) : Fin 32 :=
  (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 25 else 13) else (if j.val < 3 then 1 else 5)) else (if j.val < 6 then (if j.val < 5 then 23 else 19) else (if j.val < 7 then 8 else 28))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then 24 else 12) else (if j.val < 11 then 2 else 6)) else (if j.val < 14 then (if j.val < 13 then 22 else 18) else (if j.val < 15 then 11 else 31))))
private theorem forward_checked3 : ∀ i,
    characters.values (binaryAssignment (3 : Fin 32)) i = true →
    registry.rows 9 (forward3 i) = permutationConjugateCode conjugator3 (C.rows i) :=
  (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))
private theorem backward_checked3 : ∀ j,
    characters.values (binaryAssignment (3 : Fin 32)) (backward3 j) = true ∧
    registry.rows 9 j = permutationConjugateCode conjugator3 (C.rows (backward3 j)) :=
  (by decide +kernel)

private def conjugator7 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,7,1,6,4,3,5,2] : Array (Fin 8))[x.val]!
  invFun x := (#[0,2,7,5,4,6,3,1] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def forward7 (i : Fin 32) : Fin 16 :=
  (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 2) else (if i.val < 3 then 3 else 0)) else (if i.val < 6 then (if i.val < 5 then 0 else 4) else (if i.val < 7 then 5 else 0))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 0 else 0) else (if i.val < 11 then 0 else 1)) else (if i.val < 14 then (if i.val < 13 then 0 else 0) else (if i.val < 15 then 7 else 6)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 11 else 10) else (if i.val < 19 then 0 else 0)) else (if i.val < 22 then (if i.val < 21 then 13 else 12) else (if i.val < 23 then 0 else 0))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 0 else 0) else (if i.val < 27 then 9 else 8)) else (if i.val < 30 then (if i.val < 29 then 14 else 0) else (if i.val < 31 then 0 else 15)))))
private def backward7 (j : Fin 16) : Fin 32 :=
  (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 8 else 11) else (if j.val < 3 then 1 else 2)) else (if j.val < 6 then (if j.val < 5 then 5 else 6) else (if j.val < 7 then 15 else 14))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then 27 else 26) else (if j.val < 11 then 17 else 16)) else (if j.val < 14 then (if j.val < 13 then 21 else 20) else (if j.val < 15 then 28 else 31))))
private theorem forward_checked7 : ∀ i,
    characters.values (binaryAssignment (7 : Fin 32)) i = true →
    registry.rows 8 (forward7 i) = permutationConjugateCode conjugator7 (C.rows i) :=
  (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))
private theorem backward_checked7 : ∀ j,
    characters.values (binaryAssignment (7 : Fin 32)) (backward7 j) = true ∧
    registry.rows 8 j = permutationConjugateCode conjugator7 (C.rows (backward7 j)) :=
  (by decide +kernel)

private def conjugator11 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,2,6,3,7,1,5,4] : Array (Fin 8))[x.val]!
  invFun x := (#[0,5,1,3,7,6,2,4] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def forward11 (i : Fin 32) : Fin 16 :=
  (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 6 else 14)) else (if i.val < 6 then (if i.val < 5 then 2 else 10) else (if i.val < 7 then 0 else 0))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 3 else 11) else (if i.val < 11 then 0 else 0)) else (if i.val < 14 then (if i.val < 13 then 13 else 0) else (if i.val < 15 then 0 else 5)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 12 else 0) else (if i.val < 19 then 0 else 4)) else (if i.val < 22 then (if i.val < 21 then 0 else 9) else (if i.val < 23 then 1 else 0))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 0 else 8) else (if i.val < 27 then 0 else 0)) else (if i.val < 30 then (if i.val < 29 then 0 else 0) else (if i.val < 31 then 7 else 15)))))
private def backward11 (j : Fin 16) : Fin 32 :=
  (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 26 else 22) else (if j.val < 3 then 4 else 8)) else (if j.val < 6 then (if j.val < 5 then 19 else 15) else (if j.val < 7 then 2 else 30))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then 25 else 21) else (if j.val < 11 then 5 else 9)) else (if j.val < 14 then (if j.val < 13 then 16 else 12) else (if j.val < 15 then 3 else 31))))
private theorem forward_checked11 : ∀ i,
    characters.values (binaryAssignment (11 : Fin 32)) i = true →
    registry.rows 9 (forward11 i) = permutationConjugateCode conjugator11 (C.rows i) :=
  (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))
private theorem backward_checked11 : ∀ j,
    characters.values (binaryAssignment (11 : Fin 32)) (backward11 j) = true ∧
    registry.rows 9 j = permutationConjugateCode conjugator11 (C.rows (backward11 j)) :=
  (by decide +kernel)

private def conjugator15 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,1,2,3,4,5,6,7] : Array (Fin 8))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def forward15 (i : Fin 32) : Fin 16 :=
  (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 1)) else (if i.val < 6 then (if i.val < 5 then 2 else 3) else (if i.val < 7 then 0 else 0))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 4 else 5) else (if i.val < 11 then 0 else 0)) else (if i.val < 14 then (if i.val < 13 then 0 else 6) else (if i.val < 15 then 7 else 0)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 0 else 8) else (if i.val < 19 then 9 else 0)) else (if i.val < 22 then (if i.val < 21 then 10 else 0) else (if i.val < 23 then 0 else 11))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 12 else 0) else (if i.val < 27 then 0 else 13)) else (if i.val < 30 then (if i.val < 29 then 0 else 0) else (if i.val < 31 then 14 else 15)))))
private def backward15 (j : Fin 16) : Fin 32 :=
  (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 2 else 3) else (if j.val < 3 then 4 else 5)) else (if j.val < 6 then (if j.val < 5 then 8 else 9) else (if j.val < 7 then 13 else 14))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then 17 else 18) else (if j.val < 11 then 20 else 23)) else (if j.val < 14 then (if j.val < 13 then 24 else 27) else (if j.val < 15 then 30 else 31))))
private theorem forward_checked15 : ∀ i,
    characters.values (binaryAssignment (15 : Fin 32)) i = true →
    registry.rows 8 (forward15 i) = permutationConjugateCode conjugator15 (C.rows i) :=
  (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))
private theorem backward_checked15 : ∀ j,
    characters.values (binaryAssignment (15 : Fin 32)) (backward15 j) = true ∧
    registry.rows 8 j = permutationConjugateCode conjugator15 (C.rows (backward15 j)) :=
  (by decide +kernel)

private def conjugator19 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,2,4,1,3,5,7,6] : Array (Fin 8))[x.val]!
  invFun x := (#[0,3,1,4,2,5,7,6] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def forward19 (i : Fin 32) : Fin 16 :=
  (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 2 else 0) else (if i.val < 3 then 10 else 0)) else (if i.val < 6 then (if i.val < 5 then 0 else 6) else (if i.val < 7 then 0 else 14))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 3 else 0) else (if i.val < 11 then 11 else 0)) else (if i.val < 14 then (if i.val < 13 then 0 else 4) else (if i.val < 15 then 0 else 12)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 0 else 0) else (if i.val < 19 then 8 else 0)) else (if i.val < 22 then (if i.val < 21 then 0 else 5) else (if i.val < 23 then 0 else 13))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 1 else 0) else (if i.val < 27 then 9 else 0)) else (if i.val < 30 then (if i.val < 29 then 0 else 7) else (if i.val < 31 then 0 else 15)))))
private def backward19 (j : Fin 16) : Fin 32 :=
  (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 16 else 24) else (if j.val < 3 then 0 else 8)) else (if j.val < 6 then (if j.val < 5 then 13 else 21) else (if j.val < 7 then 5 else 29))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then 18 else 26) else (if j.val < 11 then 2 else 10)) else (if j.val < 14 then (if j.val < 13 then 15 else 23) else (if j.val < 15 then 7 else 31))))
private theorem forward_checked19 : ∀ i,
    characters.values (binaryAssignment (19 : Fin 32)) i = true →
    registry.rows 9 (forward19 i) = permutationConjugateCode conjugator19 (C.rows i) :=
  (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))
private theorem backward_checked19 : ∀ j,
    characters.values (binaryAssignment (19 : Fin 32)) (backward19 j) = true ∧
    registry.rows 9 j = permutationConjugateCode conjugator19 (C.rows (backward19 j)) :=
  (by decide +kernel)

private def conjugator23 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,1,7,4,6,3,5,2] : Array (Fin 8))[x.val]!
  invFun x := (#[0,1,7,5,3,6,4,2] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def forward23 (i : Fin 32) : Fin 16 :=
  (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 2 else 0) else (if i.val < 3 then 3 else 0)) else (if i.val < 6 then (if i.val < 5 then 0 else 0) else (if i.val < 7 then 0 else 1))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 4 else 0) else (if i.val < 11 then 5 else 0)) else (if i.val < 14 then (if i.val < 13 then 11 else 0) else (if i.val < 15 then 10 else 0)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 0 else 7) else (if i.val < 19 then 0 else 6)) else (if i.val < 22 then (if i.val < 21 then 13 else 0) else (if i.val < 23 then 12 else 0))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 0 else 9) else (if i.val < 27 then 0 else 8)) else (if i.val < 30 then (if i.val < 29 then 0 else 14) else (if i.val < 31 then 0 else 15)))))
private def backward23 (j : Fin 16) : Fin 32 :=
  (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 5 else 7) else (if j.val < 3 then 0 else 2)) else (if j.val < 6 then (if j.val < 5 then 8 else 10) else (if j.val < 7 then 19 else 17))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then 27 else 25) else (if j.val < 11 then 14 else 12)) else (if j.val < 14 then (if j.val < 13 then 22 else 20) else (if j.val < 15 then 29 else 31))))
private theorem forward_checked23 : ∀ i,
    characters.values (binaryAssignment (23 : Fin 32)) i = true →
    registry.rows 8 (forward23 i) = permutationConjugateCode conjugator23 (C.rows i) :=
  (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))
private theorem backward_checked23 : ∀ j,
    characters.values (binaryAssignment (23 : Fin 32)) (backward23 j) = true ∧
    registry.rows 8 j = permutationConjugateCode conjugator23 (C.rows (backward23 j)) :=
  (by decide +kernel)

private def conjugator31 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,1,2,3,4,5,6,7] : Array (Fin 8))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def forward31 (i : Fin 32) : Fin 32 :=
  (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 1) else (if i.val < 3 then 2 else 3)) else (if i.val < 6 then (if i.val < 5 then 4 else 5) else (if i.val < 7 then 6 else 7))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 8 else 9) else (if i.val < 11 then 10 else 11)) else (if i.val < 14 then (if i.val < 13 then 12 else 13) else (if i.val < 15 then 14 else 15)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 16 else 17) else (if i.val < 19 then 18 else 19)) else (if i.val < 22 then (if i.val < 21 then 20 else 21) else (if i.val < 23 then 22 else 23))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 24 else 25) else (if i.val < 27 then 26 else 27)) else (if i.val < 30 then (if i.val < 29 then 28 else 29) else (if i.val < 31 then 30 else 31)))))
private def backward31 (j : Fin 32) : Fin 32 :=
  (if j.val < 16 then (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 0 else 1) else (if j.val < 3 then 2 else 3)) else (if j.val < 6 then (if j.val < 5 then 4 else 5) else (if j.val < 7 then 6 else 7))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then 8 else 9) else (if j.val < 11 then 10 else 11)) else (if j.val < 14 then (if j.val < 13 then 12 else 13) else (if j.val < 15 then 14 else 15)))) else (if j.val < 24 then (if j.val < 20 then (if j.val < 18 then (if j.val < 17 then 16 else 17) else (if j.val < 19 then 18 else 19)) else (if j.val < 22 then (if j.val < 21 then 20 else 21) else (if j.val < 23 then 22 else 23))) else (if j.val < 28 then (if j.val < 26 then (if j.val < 25 then 24 else 25) else (if j.val < 27 then 26 else 27)) else (if j.val < 30 then (if j.val < 29 then 28 else 29) else (if j.val < 31 then 30 else 31)))))
private theorem forward_checked31 : ∀ i,
    characters.values (binaryAssignment (31 : Fin 32)) i = true →
    registry.rows 14 (forward31 i) = permutationConjugateCode conjugator31 (C.rows i) :=
  (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))
private theorem backward_checked31 : ∀ j,
    characters.values (binaryAssignment (31 : Fin 32)) (backward31 j) = true ∧
    registry.rows 14 j = permutationConjugateCode conjugator31 (C.rows (backward31 j)) :=
  (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))

private theorem checked : ∀ bits : Fin 5 → Bool,
    (∀ i j, characters.values bits (C.next i j) = (characters.values bits i == bits j)) →
    (∀ y : Fin 8, ∃ i, characters.values bits i = true ∧ encodedRowAction C i 0 = y) →
    ∃ k, ∃ g : Equiv.Perm (Fin 8),
      (∀ i, characters.values bits i = true →
        ∃ j, registry.rows k j = permutationConjugateCode g (C.rows i)) ∧
      (∀ j, ∃ i, characters.values bits i = true ∧
        registry.rows k j = permutationConjugateCode g (C.rows i)) := by
  intro bits
  obtain ⟨b,rfl⟩ := binaryAssignment_surjective 5 bits
  fin_cases b
  · intro hs _
    exact False.elim ((show ¬(∀ i j, characters.values (binaryAssignment (0 : Fin 32))
      (C.next i j) = (characters.values (binaryAssignment (0 : Fin 32)) i ==
        binaryAssignment (0 : Fin 32) j)) from by decide +kernel) hs)
  · intro hs _
    exact False.elim ((show ¬(∀ i j, characters.values (binaryAssignment (1 : Fin 32))
      (C.next i j) = (characters.values (binaryAssignment (1 : Fin 32)) i ==
        binaryAssignment (1 : Fin 32) j)) from by decide +kernel) hs)
  · intro hs _
    exact False.elim ((show ¬(∀ i j, characters.values (binaryAssignment (2 : Fin 32))
      (C.next i j) = (characters.values (binaryAssignment (2 : Fin 32)) i ==
        binaryAssignment (2 : Fin 32) j)) from by decide +kernel) hs)
  · intro _ _
    exact ⟨9,conjugator3,
      fun i hi => ⟨forward3 i,forward_checked3 i hi⟩,
      fun j => ⟨backward3 j,backward_checked3 j⟩⟩
  · intro hs _
    exact False.elim ((show ¬(∀ i j, characters.values (binaryAssignment (4 : Fin 32))
      (C.next i j) = (characters.values (binaryAssignment (4 : Fin 32)) i ==
        binaryAssignment (4 : Fin 32) j)) from by decide +kernel) hs)
  · intro hs _
    exact False.elim ((show ¬(∀ i j, characters.values (binaryAssignment (5 : Fin 32))
      (C.next i j) = (characters.values (binaryAssignment (5 : Fin 32)) i ==
        binaryAssignment (5 : Fin 32) j)) from by decide +kernel) hs)
  · intro hs _
    exact False.elim ((show ¬(∀ i j, characters.values (binaryAssignment (6 : Fin 32))
      (C.next i j) = (characters.values (binaryAssignment (6 : Fin 32)) i ==
        binaryAssignment (6 : Fin 32) j)) from by decide +kernel) hs)
  · intro _ _
    exact ⟨8,conjugator7,
      fun i hi => ⟨forward7 i,forward_checked7 i hi⟩,
      fun j => ⟨backward7 j,backward_checked7 j⟩⟩
  · intro hs _
    exact False.elim ((show ¬(∀ i j, characters.values (binaryAssignment (8 : Fin 32))
      (C.next i j) = (characters.values (binaryAssignment (8 : Fin 32)) i ==
        binaryAssignment (8 : Fin 32) j)) from by decide +kernel) hs)
  · intro hs _
    exact False.elim ((show ¬(∀ i j, characters.values (binaryAssignment (9 : Fin 32))
      (C.next i j) = (characters.values (binaryAssignment (9 : Fin 32)) i ==
        binaryAssignment (9 : Fin 32) j)) from by decide +kernel) hs)
  · intro hs _
    exact False.elim ((show ¬(∀ i j, characters.values (binaryAssignment (10 : Fin 32))
      (C.next i j) = (characters.values (binaryAssignment (10 : Fin 32)) i ==
        binaryAssignment (10 : Fin 32) j)) from by decide +kernel) hs)
  · intro _ _
    exact ⟨9,conjugator11,
      fun i hi => ⟨forward11 i,forward_checked11 i hi⟩,
      fun j => ⟨backward11 j,backward_checked11 j⟩⟩
  · intro hs _
    exact False.elim ((show ¬(∀ i j, characters.values (binaryAssignment (12 : Fin 32))
      (C.next i j) = (characters.values (binaryAssignment (12 : Fin 32)) i ==
        binaryAssignment (12 : Fin 32) j)) from by decide +kernel) hs)
  · intro hs _
    exact False.elim ((show ¬(∀ i j, characters.values (binaryAssignment (13 : Fin 32))
      (C.next i j) = (characters.values (binaryAssignment (13 : Fin 32)) i ==
        binaryAssignment (13 : Fin 32) j)) from by decide +kernel) hs)
  · intro hs _
    exact False.elim ((show ¬(∀ i j, characters.values (binaryAssignment (14 : Fin 32))
      (C.next i j) = (characters.values (binaryAssignment (14 : Fin 32)) i ==
        binaryAssignment (14 : Fin 32) j)) from by decide +kernel) hs)
  · intro _ _
    exact ⟨8,conjugator15,
      fun i hi => ⟨forward15 i,forward_checked15 i hi⟩,
      fun j => ⟨backward15 j,backward_checked15 j⟩⟩
  · intro hs _
    exact False.elim ((show ¬(∀ i j, characters.values (binaryAssignment (16 : Fin 32))
      (C.next i j) = (characters.values (binaryAssignment (16 : Fin 32)) i ==
        binaryAssignment (16 : Fin 32) j)) from by decide +kernel) hs)
  · intro hs _
    exact False.elim ((show ¬(∀ i j, characters.values (binaryAssignment (17 : Fin 32))
      (C.next i j) = (characters.values (binaryAssignment (17 : Fin 32)) i ==
        binaryAssignment (17 : Fin 32) j)) from by decide +kernel) hs)
  · intro hs _
    exact False.elim ((show ¬(∀ i j, characters.values (binaryAssignment (18 : Fin 32))
      (C.next i j) = (characters.values (binaryAssignment (18 : Fin 32)) i ==
        binaryAssignment (18 : Fin 32) j)) from by decide +kernel) hs)
  · intro _ _
    exact ⟨9,conjugator19,
      fun i hi => ⟨forward19 i,forward_checked19 i hi⟩,
      fun j => ⟨backward19 j,backward_checked19 j⟩⟩
  · intro hs _
    exact False.elim ((show ¬(∀ i j, characters.values (binaryAssignment (20 : Fin 32))
      (C.next i j) = (characters.values (binaryAssignment (20 : Fin 32)) i ==
        binaryAssignment (20 : Fin 32) j)) from by decide +kernel) hs)
  · intro hs _
    exact False.elim ((show ¬(∀ i j, characters.values (binaryAssignment (21 : Fin 32))
      (C.next i j) = (characters.values (binaryAssignment (21 : Fin 32)) i ==
        binaryAssignment (21 : Fin 32) j)) from by decide +kernel) hs)
  · intro hs _
    exact False.elim ((show ¬(∀ i j, characters.values (binaryAssignment (22 : Fin 32))
      (C.next i j) = (characters.values (binaryAssignment (22 : Fin 32)) i ==
        binaryAssignment (22 : Fin 32) j)) from by decide +kernel) hs)
  · intro _ _
    exact ⟨8,conjugator23,
      fun i hi => ⟨forward23 i,forward_checked23 i hi⟩,
      fun j => ⟨backward23 j,backward_checked23 j⟩⟩
  · intro hs _
    exact False.elim ((show ¬(∀ i j, characters.values (binaryAssignment (24 : Fin 32))
      (C.next i j) = (characters.values (binaryAssignment (24 : Fin 32)) i ==
        binaryAssignment (24 : Fin 32) j)) from by decide +kernel) hs)
  · intro hs _
    exact False.elim ((show ¬(∀ i j, characters.values (binaryAssignment (25 : Fin 32))
      (C.next i j) = (characters.values (binaryAssignment (25 : Fin 32)) i ==
        binaryAssignment (25 : Fin 32) j)) from by decide +kernel) hs)
  · intro hs _
    exact False.elim ((show ¬(∀ i j, characters.values (binaryAssignment (26 : Fin 32))
      (C.next i j) = (characters.values (binaryAssignment (26 : Fin 32)) i ==
        binaryAssignment (26 : Fin 32) j)) from by decide +kernel) hs)
  · intro _ ht
    exact False.elim ((show ¬(∀ y : Fin 8, ∃ i,
      characters.values (binaryAssignment (27 : Fin 32)) i = true ∧
        encodedRowAction C i 0 = y) from by decide +kernel) ht)
  · intro hs _
    exact False.elim ((show ¬(∀ i j, characters.values (binaryAssignment (28 : Fin 32))
      (C.next i j) = (characters.values (binaryAssignment (28 : Fin 32)) i ==
        binaryAssignment (28 : Fin 32) j)) from by decide +kernel) hs)
  · intro hs _
    exact False.elim ((show ¬(∀ i j, characters.values (binaryAssignment (29 : Fin 32))
      (C.next i j) = (characters.values (binaryAssignment (29 : Fin 32)) i ==
        binaryAssignment (29 : Fin 32) j)) from by decide +kernel) hs)
  · intro hs _
    exact False.elim ((show ¬(∀ i j, characters.values (binaryAssignment (30 : Fin 32))
      (C.next i j) = (characters.values (binaryAssignment (30 : Fin 32)) i ==
        binaryAssignment (30 : Fin 32) j)) from by decide +kernel) hs)
  · intro _ _
    exact ⟨14,conjugator31,
      fun i hi => ⟨forward31 i,forward_checked31 i hi⟩,
      fun j => ⟨backward31 j,backward_checked31 j⟩⟩

/-- Complete literal transitive index-two child coverage for this original action. -/
theorem children (K : Subgroup (Equiv.Perm (Fin 8)))
    (hle : K ≤ Subgroup.closure (Set.range BinaryMenuCayley8T18.generators))
    (hindex : K.relIndex (Subgroup.closure (Set.range BinaryMenuCayley8T18.generators)) = 2)
    (ht : PermutationSubgroupTransitive K) : ActionRegistryCovered actions K :=
  binary_character_registry_children C characters actions registry 0 checked K hle hindex ht

end SymmetricSubgroupAsymptotics.BinaryActionChildren8T18
