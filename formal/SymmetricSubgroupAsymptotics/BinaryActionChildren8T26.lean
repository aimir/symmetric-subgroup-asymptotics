import SymmetricSubgroupAsymptotics.BinaryActionRegistry8

/-! All original index-two transitive children of b8_26, checked by generator bits. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryActionChildren8T26
open BinaryActionRegistry8
private def C := BinaryMenuCayley8T26.certificate
private def values (bits : Fin 3 → Bool) (i : Fin 64) : Bool :=
  (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then ((true == bits 0) == bits 2) else (((true == bits 0) == bits 1) == bits 2)) else (if i.val < 3 then ((true == bits 0) == bits 1) else (true == bits 0))) else (if i.val < 6 then (if i.val < 5 then ((true == bits 0) == bits 2) else (((true == bits 0) == bits 1) == bits 2)) else (if i.val < 7 then ((true == bits 0) == bits 1) else (true == bits 0)))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then (true == bits 1) else true) else (if i.val < 11 then (true == bits 2) else ((true == bits 1) == bits 2))) else (if i.val < 14 then (if i.val < 13 then (true == bits 1) else true) else (if i.val < 15 then (true == bits 2) else ((true == bits 1) == bits 2))))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then (true == bits 0) else ((true == bits 0) == bits 1)) else (if i.val < 19 then (((true == bits 0) == bits 1) == bits 2) else ((true == bits 0) == bits 2))) else (if i.val < 22 then (if i.val < 21 then (true == bits 0) else ((true == bits 0) == bits 1)) else (if i.val < 23 then (((true == bits 0) == bits 1) == bits 2) else ((true == bits 0) == bits 2)))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then ((true == bits 1) == bits 2) else (true == bits 2)) else (if i.val < 27 then true else (true == bits 1))) else (if i.val < 30 then (if i.val < 29 then ((true == bits 1) == bits 2) else (true == bits 2)) else (if i.val < 31 then true else (true == bits 1)))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then (((true == bits 0) == bits 1) == bits 2) else ((true == bits 0) == bits 2)) else (if i.val < 35 then (true == bits 0) else ((true == bits 0) == bits 1))) else (if i.val < 38 then (if i.val < 37 then (((true == bits 0) == bits 1) == bits 2) else ((true == bits 0) == bits 2)) else (if i.val < 39 then (true == bits 0) else ((true == bits 0) == bits 1)))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then true else (true == bits 1)) else (if i.val < 43 then ((true == bits 1) == bits 2) else (true == bits 2))) else (if i.val < 46 then (if i.val < 45 then true else (true == bits 1)) else (if i.val < 47 then ((true == bits 1) == bits 2) else (true == bits 2))))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then ((true == bits 0) == bits 1) else (true == bits 0)) else (if i.val < 51 then ((true == bits 0) == bits 2) else (((true == bits 0) == bits 1) == bits 2))) else (if i.val < 54 then (if i.val < 53 then ((true == bits 0) == bits 1) else (true == bits 0)) else (if i.val < 55 then ((true == bits 0) == bits 2) else (((true == bits 0) == bits 1) == bits 2)))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then (true == bits 2) else ((true == bits 1) == bits 2)) else (if i.val < 59 then (true == bits 1) else true)) else (if i.val < 62 then (if i.val < 61 then (true == bits 2) else ((true == bits 1) == bits 2)) else (if i.val < 63 then (true == bits 1) else true))))))
private def characters : BinaryRowCharacters C where
  values := values
  identity_eq := by decide +kernel
  parent_eq := by decide +kernel

private def conjugator0 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,4,1,3,2,6,7,5] : Array (Fin 8))[x.val]!
  invFun x := (#[0,2,4,3,1,7,5,6] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def forward0 (i : Fin 64) : Fin 32 :=
  (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 17 else 0) else (if i.val < 3 then 13 else 0)) else (if i.val < 6 then (if i.val < 5 then 25 else 0) else (if i.val < 7 then 21 else 0))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 0 else 2) else (if i.val < 11 then 0 else 6)) else (if i.val < 14 then (if i.val < 13 then 0 else 10) else (if i.val < 15 then 0 else 30)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 0 else 18) else (if i.val < 19 then 0 else 14)) else (if i.val < 22 then (if i.val < 21 then 0 else 26) else (if i.val < 23 then 0 else 22))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 1 else 0) else (if i.val < 27 then 5 else 0)) else (if i.val < 30 then (if i.val < 29 then 9 else 0) else (if i.val < 31 then 29 else 0))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 0 else 19) else (if i.val < 35 then 0 else 15)) else (if i.val < 38 then (if i.val < 37 then 0 else 27) else (if i.val < 39 then 0 else 23))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 0 else 0) else (if i.val < 43 then 4 else 0)) else (if i.val < 46 then (if i.val < 45 then 8 else 0) else (if i.val < 47 then 28 else 0)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 16 else 0) else (if i.val < 51 then 12 else 0)) else (if i.val < 54 then (if i.val < 53 then 24 else 0) else (if i.val < 55 then 20 else 0))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 0 else 3) else (if i.val < 59 then 0 else 7)) else (if i.val < 62 then (if i.val < 61 then 0 else 11) else (if i.val < 63 then 0 else 31))))))
private def backward0 (j : Fin 32) : Fin 64 :=
  (if j.val < 16 then (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 40 else 24) else (if j.val < 3 then 9 else 57)) else (if j.val < 6 then (if j.val < 5 then 42 else 26) else (if j.val < 7 then 11 else 59))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then 44 else 28) else (if j.val < 11 then 13 else 61)) else (if j.val < 14 then (if j.val < 13 then 50 else 2) else (if j.val < 15 then 19 else 35)))) else (if j.val < 24 then (if j.val < 20 then (if j.val < 18 then (if j.val < 17 then 48 else 0) else (if j.val < 19 then 17 else 33)) else (if j.val < 22 then (if j.val < 21 then 54 else 6) else (if j.val < 23 then 23 else 39))) else (if j.val < 28 then (if j.val < 26 then (if j.val < 25 then 52 else 4) else (if j.val < 27 then 21 else 37)) else (if j.val < 30 then (if j.val < 29 then 46 else 30) else (if j.val < 31 then 15 else 63)))))
private theorem forward_checked0 : ∀ i,
    characters.values (binaryAssignment (0 : Fin 8)) i = true →
    registry.rows 13 (forward0 i) = permutationConjugateCode conjugator0 (C.rows i) :=
  (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))
private theorem backward_checked0 : ∀ j,
    characters.values (binaryAssignment (0 : Fin 8)) (backward0 j) = true ∧
    registry.rows 13 j = permutationConjugateCode conjugator0 (C.rows (backward0 j)) :=
  (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))

private def conjugator1 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,3,1,4,2,5,7,6] : Array (Fin 8))[x.val]!
  invFun x := (#[0,2,4,1,3,5,7,6] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def forward1 (i : Fin 64) : Fin 32 :=
  (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 12) else (if i.val < 3 then 0 else 16)) else (if i.val < 6 then (if i.val < 5 then 0 else 20) else (if i.val < 7 then 0 else 24))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 0 else 0) else (if i.val < 11 then 0 else 4)) else (if i.val < 14 then (if i.val < 13 then 0 else 8) else (if i.val < 15 then 0 else 28)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 13 else 0) else (if i.val < 19 then 17 else 0)) else (if i.val < 22 then (if i.val < 21 then 21 else 0) else (if i.val < 23 then 25 else 0))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 1 else 0) else (if i.val < 27 then 5 else 0)) else (if i.val < 30 then (if i.val < 29 then 9 else 0) else (if i.val < 31 then 29 else 0))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 14 else 0) else (if i.val < 35 then 18 else 0)) else (if i.val < 38 then (if i.val < 37 then 22 else 0) else (if i.val < 39 then 26 else 0))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 2 else 0) else (if i.val < 43 then 6 else 0)) else (if i.val < 46 then (if i.val < 45 then 10 else 0) else (if i.val < 47 then 30 else 0)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 0 else 15) else (if i.val < 51 then 0 else 19)) else (if i.val < 54 then (if i.val < 53 then 0 else 23) else (if i.val < 55 then 0 else 27))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 0 else 3) else (if i.val < 59 then 0 else 7)) else (if i.val < 62 then (if i.val < 61 then 0 else 11) else (if i.val < 63 then 0 else 31))))))
private def backward1 (j : Fin 32) : Fin 64 :=
  (if j.val < 16 then (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 9 else 24) else (if j.val < 3 then 40 else 57)) else (if j.val < 6 then (if j.val < 5 then 11 else 26) else (if j.val < 7 then 42 else 59))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then 13 else 28) else (if j.val < 11 then 44 else 61)) else (if j.val < 14 then (if j.val < 13 then 1 else 16) else (if j.val < 15 then 32 else 49)))) else (if j.val < 24 then (if j.val < 20 then (if j.val < 18 then (if j.val < 17 then 3 else 18) else (if j.val < 19 then 34 else 51)) else (if j.val < 22 then (if j.val < 21 then 5 else 20) else (if j.val < 23 then 36 else 53))) else (if j.val < 28 then (if j.val < 26 then (if j.val < 25 then 7 else 22) else (if j.val < 27 then 38 else 55)) else (if j.val < 30 then (if j.val < 29 then 15 else 30) else (if j.val < 31 then 46 else 63)))))
private theorem forward_checked1 : ∀ i,
    characters.values (binaryAssignment (1 : Fin 8)) i = true →
    registry.rows 13 (forward1 i) = permutationConjugateCode conjugator1 (C.rows i) :=
  (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))
private theorem backward_checked1 : ∀ j,
    characters.values (binaryAssignment (1 : Fin 8)) (backward1 j) = true ∧
    registry.rows 13 j = permutationConjugateCode conjugator1 (C.rows (backward1 j)) :=
  (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))

private def conjugator2 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,1,3,5,7,2,4,6] : Array (Fin 8))[x.val]!
  invFun x := (#[0,1,5,2,6,3,7,4] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def forward2 (i : Fin 64) : Fin 32 :=
  (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 20 else 24) else (if i.val < 3 then 0 else 0)) else (if i.val < 6 then (if i.val < 5 then 25 else 21) else (if i.val < 7 then 0 else 0))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 12 else 16) else (if i.val < 11 then 0 else 0)) else (if i.val < 14 then (if i.val < 13 then 17 else 13) else (if i.val < 15 then 0 else 0)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 0 else 0) else (if i.val < 19 then 4 else 8)) else (if i.val < 22 then (if i.val < 21 then 0 else 0) else (if i.val < 23 then 9 else 5))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 0 else 0) else (if i.val < 27 then 0 else 28)) else (if i.val < 30 then (if i.val < 29 then 0 else 0) else (if i.val < 31 then 29 else 1))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 26 else 22) else (if i.val < 35 then 0 else 0)) else (if i.val < 38 then (if i.val < 37 then 23 else 27) else (if i.val < 39 then 0 else 0))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 18 else 14) else (if i.val < 43 then 0 else 0)) else (if i.val < 46 then (if i.val < 45 then 15 else 19) else (if i.val < 47 then 0 else 0)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 0 else 0) else (if i.val < 51 then 10 else 6)) else (if i.val < 54 then (if i.val < 53 then 0 else 0) else (if i.val < 55 then 7 else 11))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 0 else 0) else (if i.val < 59 then 30 else 2)) else (if i.val < 62 then (if i.val < 61 then 0 else 0) else (if i.val < 63 then 3 else 31))))))
private def backward2 (j : Fin 32) : Fin 64 :=
  (if j.val < 16 then (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 26 else 31) else (if j.val < 3 then 59 else 62)) else (if j.val < 6 then (if j.val < 5 then 18 else 23) else (if j.val < 7 then 51 else 54))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then 19 else 22) else (if j.val < 11 then 50 else 55)) else (if j.val < 14 then (if j.val < 13 then 8 else 13) else (if j.val < 15 then 41 else 44)))) else (if j.val < 24 then (if j.val < 20 then (if j.val < 18 then (if j.val < 17 then 9 else 12) else (if j.val < 19 then 40 else 45)) else (if j.val < 22 then (if j.val < 21 then 0 else 5) else (if j.val < 23 then 33 else 36))) else (if j.val < 28 then (if j.val < 26 then (if j.val < 25 then 1 else 4) else (if j.val < 27 then 32 else 37)) else (if j.val < 30 then (if j.val < 29 then 27 else 30) else (if j.val < 31 then 58 else 63)))))
private theorem forward_checked2 : ∀ i,
    characters.values (binaryAssignment (2 : Fin 8)) i = true →
    registry.rows 18 (forward2 i) = permutationConjugateCode conjugator2 (C.rows i) :=
  (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))
private theorem backward_checked2 : ∀ j,
    characters.values (binaryAssignment (2 : Fin 8)) (backward2 j) = true ∧
    registry.rows 18 j = permutationConjugateCode conjugator2 (C.rows (backward2 j)) :=
  (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))

private def conjugator3 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,1,2,3,4,5,6,7] : Array (Fin 8))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def forward3 (i : Fin 64) : Fin 32 :=
  (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 1)) else (if i.val < 6 then (if i.val < 5 then 0 else 0) else (if i.val < 7 then 2 else 3))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 4 else 5) else (if i.val < 11 then 0 else 0)) else (if i.val < 14 then (if i.val < 13 then 6 else 7) else (if i.val < 15 then 0 else 0)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 8 else 9) else (if i.val < 19 then 0 else 0)) else (if i.val < 22 then (if i.val < 21 then 10 else 11) else (if i.val < 23 then 0 else 0))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 0 else 0) else (if i.val < 27 then 12 else 13)) else (if i.val < 30 then (if i.val < 29 then 0 else 0) else (if i.val < 31 then 14 else 15))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 0 else 0) else (if i.val < 35 then 16 else 17)) else (if i.val < 38 then (if i.val < 37 then 0 else 0) else (if i.val < 39 then 18 else 19))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 20 else 21) else (if i.val < 43 then 0 else 0)) else (if i.val < 46 then (if i.val < 45 then 22 else 23) else (if i.val < 47 then 0 else 0)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 24 else 25) else (if i.val < 51 then 0 else 0)) else (if i.val < 54 then (if i.val < 53 then 26 else 27) else (if i.val < 55 then 0 else 0))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 0 else 0) else (if i.val < 59 then 28 else 29)) else (if i.val < 62 then (if i.val < 61 then 0 else 0) else (if i.val < 63 then 30 else 31))))))
private def backward3 (j : Fin 32) : Fin 64 :=
  (if j.val < 16 then (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 2 else 3) else (if j.val < 3 then 6 else 7)) else (if j.val < 6 then (if j.val < 5 then 8 else 9) else (if j.val < 7 then 12 else 13))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then 16 else 17) else (if j.val < 11 then 20 else 21)) else (if j.val < 14 then (if j.val < 13 then 26 else 27) else (if j.val < 15 then 30 else 31)))) else (if j.val < 24 then (if j.val < 20 then (if j.val < 18 then (if j.val < 17 then 34 else 35) else (if j.val < 19 then 38 else 39)) else (if j.val < 22 then (if j.val < 21 then 40 else 41) else (if j.val < 23 then 44 else 45))) else (if j.val < 28 then (if j.val < 26 then (if j.val < 25 then 48 else 49) else (if j.val < 27 then 52 else 53)) else (if j.val < 30 then (if j.val < 29 then 58 else 59) else (if j.val < 31 then 62 else 63)))))
private theorem forward_checked3 : ∀ i,
    characters.values (binaryAssignment (3 : Fin 8)) i = true →
    registry.rows 12 (forward3 i) = permutationConjugateCode conjugator3 (C.rows i) :=
  (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))
private theorem backward_checked3 : ∀ j,
    characters.values (binaryAssignment (3 : Fin 8)) (backward3 j) = true ∧
    registry.rows 12 j = permutationConjugateCode conjugator3 (C.rows (backward3 j)) :=
  (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))

private def conjugator4 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,7,6,1,4,3,2,5] : Array (Fin 8))[x.val]!
  invFun x := (#[0,3,6,5,4,7,2,1] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def forward4 (i : Fin 64) : Fin 32 :=
  (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 25) else (if i.val < 3 then 10 else 0)) else (if i.val < 6 then (if i.val < 5 then 0 else 27) else (if i.val < 7 then 8 else 0))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 0 else 6) else (if i.val < 11 then 21 else 0)) else (if i.val < 14 then (if i.val < 13 then 0 else 4) else (if i.val < 15 then 23 else 0)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 0 else 1) else (if i.val < 19 then 18 else 0)) else (if i.val < 22 then (if i.val < 21 then 0 else 3) else (if i.val < 23 then 16 else 0))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 0 else 30) else (if i.val < 27 then 13 else 0)) else (if i.val < 30 then (if i.val < 29 then 0 else 28) else (if i.val < 31 then 15 else 0))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 9 else 0) else (if i.val < 35 then 0 else 26)) else (if i.val < 38 then (if i.val < 37 then 11 else 0) else (if i.val < 39 then 0 else 24))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 22 else 0) else (if i.val < 43 then 0 else 5)) else (if i.val < 46 then (if i.val < 45 then 20 else 0) else (if i.val < 47 then 0 else 7)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 17 else 0) else (if i.val < 51 then 0 else 2)) else (if i.val < 54 then (if i.val < 53 then 19 else 0) else (if i.val < 55 then 0 else 0))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 14 else 0) else (if i.val < 59 then 0 else 29)) else (if i.val < 62 then (if i.val < 61 then 12 else 0) else (if i.val < 63 then 0 else 31))))))
private def backward4 (j : Fin 32) : Fin 64 :=
  (if j.val < 16 then (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 55 else 17) else (if j.val < 3 then 51 else 21)) else (if j.val < 6 then (if j.val < 5 then 13 else 43) else (if j.val < 7 then 9 else 47))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then 6 else 32) else (if j.val < 11 then 2 else 36)) else (if j.val < 14 then (if j.val < 13 then 60 else 26) else (if j.val < 15 then 56 else 30)))) else (if j.val < 24 then (if j.val < 20 then (if j.val < 18 then (if j.val < 17 then 22 else 48) else (if j.val < 19 then 18 else 52)) else (if j.val < 22 then (if j.val < 21 then 44 else 10) else (if j.val < 23 then 40 else 14))) else (if j.val < 28 then (if j.val < 26 then (if j.val < 25 then 39 else 1) else (if j.val < 27 then 35 else 5)) else (if j.val < 30 then (if j.val < 29 then 29 else 59) else (if j.val < 31 then 25 else 63)))))
private theorem forward_checked4 : ∀ i,
    characters.values (binaryAssignment (4 : Fin 8)) i = true →
    registry.rows 11 (forward4 i) = permutationConjugateCode conjugator4 (C.rows i) :=
  (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))
private theorem backward_checked4 : ∀ j,
    characters.values (binaryAssignment (4 : Fin 8)) (backward4 j) = true ∧
    registry.rows 11 j = permutationConjugateCode conjugator4 (C.rows (backward4 j)) :=
  (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))

private def conjugator5 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,1,2,3,4,5,6,7] : Array (Fin 8))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def forward5 (i : Fin 64) : Fin 32 :=
  (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 1)) else (if i.val < 6 then (if i.val < 5 then 2 else 0) else (if i.val < 7 then 0 else 3))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 0 else 4) else (if i.val < 11 then 5 else 0)) else (if i.val < 14 then (if i.val < 13 then 0 else 6) else (if i.val < 15 then 7 else 0)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 8 else 0) else (if i.val < 19 then 0 else 9)) else (if i.val < 22 then (if i.val < 21 then 10 else 0) else (if i.val < 23 then 0 else 11))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 0 else 12) else (if i.val < 27 then 13 else 0)) else (if i.val < 30 then (if i.val < 29 then 0 else 14) else (if i.val < 31 then 15 else 0))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 0 else 16) else (if i.val < 35 then 17 else 0)) else (if i.val < 38 then (if i.val < 37 then 0 else 18) else (if i.val < 39 then 19 else 0))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 20 else 0) else (if i.val < 43 then 0 else 21)) else (if i.val < 46 then (if i.val < 45 then 22 else 0) else (if i.val < 47 then 0 else 23)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 0 else 24) else (if i.val < 51 then 25 else 0)) else (if i.val < 54 then (if i.val < 53 then 0 else 26) else (if i.val < 55 then 27 else 0))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 28 else 0) else (if i.val < 59 then 0 else 29)) else (if i.val < 62 then (if i.val < 61 then 30 else 0) else (if i.val < 63 then 0 else 31))))))
private def backward5 (j : Fin 32) : Fin 64 :=
  (if j.val < 16 then (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 0 else 3) else (if j.val < 3 then 4 else 7)) else (if j.val < 6 then (if j.val < 5 then 9 else 10) else (if j.val < 7 then 13 else 14))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then 16 else 19) else (if j.val < 11 then 20 else 23)) else (if j.val < 14 then (if j.val < 13 then 25 else 26) else (if j.val < 15 then 29 else 30)))) else (if j.val < 24 then (if j.val < 20 then (if j.val < 18 then (if j.val < 17 then 33 else 34) else (if j.val < 19 then 37 else 38)) else (if j.val < 22 then (if j.val < 21 then 40 else 43) else (if j.val < 23 then 44 else 47))) else (if j.val < 28 then (if j.val < 26 then (if j.val < 25 then 49 else 50) else (if j.val < 27 then 53 else 54)) else (if j.val < 30 then (if j.val < 29 then 56 else 59) else (if j.val < 31 then 60 else 63)))))
private theorem forward_checked5 : ∀ i,
    characters.values (binaryAssignment (5 : Fin 8)) i = true →
    registry.rows 11 (forward5 i) = permutationConjugateCode conjugator5 (C.rows i) :=
  (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))
private theorem backward_checked5 : ∀ j,
    characters.values (binaryAssignment (5 : Fin 8)) (backward5 j) = true ∧
    registry.rows 11 j = permutationConjugateCode conjugator5 (C.rows (backward5 j)) :=
  (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))

private def conjugator7 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,1,2,3,4,5,6,7] : Array (Fin 8))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def forward7 (i : Fin 64) : Fin 64 :=
  (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 1) else (if i.val < 3 then 2 else 3)) else (if i.val < 6 then (if i.val < 5 then 4 else 5) else (if i.val < 7 then 6 else 7))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 8 else 9) else (if i.val < 11 then 10 else 11)) else (if i.val < 14 then (if i.val < 13 then 12 else 13) else (if i.val < 15 then 14 else 15)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 16 else 17) else (if i.val < 19 then 18 else 19)) else (if i.val < 22 then (if i.val < 21 then 20 else 21) else (if i.val < 23 then 22 else 23))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 24 else 25) else (if i.val < 27 then 26 else 27)) else (if i.val < 30 then (if i.val < 29 then 28 else 29) else (if i.val < 31 then 30 else 31))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 32 else 33) else (if i.val < 35 then 34 else 35)) else (if i.val < 38 then (if i.val < 37 then 36 else 37) else (if i.val < 39 then 38 else 39))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 40 else 41) else (if i.val < 43 then 42 else 43)) else (if i.val < 46 then (if i.val < 45 then 44 else 45) else (if i.val < 47 then 46 else 47)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 48 else 49) else (if i.val < 51 then 50 else 51)) else (if i.val < 54 then (if i.val < 53 then 52 else 53) else (if i.val < 55 then 54 else 55))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 56 else 57) else (if i.val < 59 then 58 else 59)) else (if i.val < 62 then (if i.val < 61 then 60 else 61) else (if i.val < 63 then 62 else 63))))))
private def backward7 (j : Fin 64) : Fin 64 :=
  (if j.val < 32 then (if j.val < 16 then (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 0 else 1) else (if j.val < 3 then 2 else 3)) else (if j.val < 6 then (if j.val < 5 then 4 else 5) else (if j.val < 7 then 6 else 7))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then 8 else 9) else (if j.val < 11 then 10 else 11)) else (if j.val < 14 then (if j.val < 13 then 12 else 13) else (if j.val < 15 then 14 else 15)))) else (if j.val < 24 then (if j.val < 20 then (if j.val < 18 then (if j.val < 17 then 16 else 17) else (if j.val < 19 then 18 else 19)) else (if j.val < 22 then (if j.val < 21 then 20 else 21) else (if j.val < 23 then 22 else 23))) else (if j.val < 28 then (if j.val < 26 then (if j.val < 25 then 24 else 25) else (if j.val < 27 then 26 else 27)) else (if j.val < 30 then (if j.val < 29 then 28 else 29) else (if j.val < 31 then 30 else 31))))) else (if j.val < 48 then (if j.val < 40 then (if j.val < 36 then (if j.val < 34 then (if j.val < 33 then 32 else 33) else (if j.val < 35 then 34 else 35)) else (if j.val < 38 then (if j.val < 37 then 36 else 37) else (if j.val < 39 then 38 else 39))) else (if j.val < 44 then (if j.val < 42 then (if j.val < 41 then 40 else 41) else (if j.val < 43 then 42 else 43)) else (if j.val < 46 then (if j.val < 45 then 44 else 45) else (if j.val < 47 then 46 else 47)))) else (if j.val < 56 then (if j.val < 52 then (if j.val < 50 then (if j.val < 49 then 48 else 49) else (if j.val < 51 then 50 else 51)) else (if j.val < 54 then (if j.val < 53 then 52 else 53) else (if j.val < 55 then 54 else 55))) else (if j.val < 60 then (if j.val < 58 then (if j.val < 57 then 56 else 57) else (if j.val < 59 then 58 else 59)) else (if j.val < 62 then (if j.val < 61 then 60 else 61) else (if j.val < 63 then 62 else 63))))))
private theorem forward_checked7 : ∀ i,
    characters.values (binaryAssignment (7 : Fin 8)) i = true →
    registry.rows 19 (forward7 i) = permutationConjugateCode conjugator7 (C.rows i) :=
  (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))
private theorem backward_checked7 : ∀ j,
    characters.values (binaryAssignment (7 : Fin 8)) (backward7 j) = true ∧
    registry.rows 19 j = permutationConjugateCode conjugator7 (C.rows (backward7 j)) :=
  (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))

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
    exact ⟨13,conjugator0,
      fun i hi => ⟨forward0 i,forward_checked0 i hi⟩,
      fun j => ⟨backward0 j,backward_checked0 j⟩⟩
  · intro _ _
    exact ⟨13,conjugator1,
      fun i hi => ⟨forward1 i,forward_checked1 i hi⟩,
      fun j => ⟨backward1 j,backward_checked1 j⟩⟩
  · intro _ _
    exact ⟨18,conjugator2,
      fun i hi => ⟨forward2 i,forward_checked2 i hi⟩,
      fun j => ⟨backward2 j,backward_checked2 j⟩⟩
  · intro _ _
    exact ⟨12,conjugator3,
      fun i hi => ⟨forward3 i,forward_checked3 i hi⟩,
      fun j => ⟨backward3 j,backward_checked3 j⟩⟩
  · intro _ _
    exact ⟨11,conjugator4,
      fun i hi => ⟨forward4 i,forward_checked4 i hi⟩,
      fun j => ⟨backward4 j,backward_checked4 j⟩⟩
  · intro _ _
    exact ⟨11,conjugator5,
      fun i hi => ⟨forward5 i,forward_checked5 i hi⟩,
      fun j => ⟨backward5 j,backward_checked5 j⟩⟩
  · intro _ ht
    exact False.elim ((show ¬(∀ y : Fin 8, ∃ i,
      characters.values (binaryAssignment (6 : Fin 8)) i = true ∧
        encodedRowAction C i 0 = y) from by decide +kernel) ht)
  · intro _ _
    exact ⟨19,conjugator7,
      fun i hi => ⟨forward7 i,forward_checked7 i hi⟩,
      fun j => ⟨backward7 j,backward_checked7 j⟩⟩

/-- Complete literal transitive index-two child coverage for this original action. -/
theorem children (K : Subgroup (Equiv.Perm (Fin 8)))
    (hle : K ≤ Subgroup.closure (Set.range BinaryMenuCayley8T26.generators))
    (hindex : K.relIndex (Subgroup.closure (Set.range BinaryMenuCayley8T26.generators)) = 2)
    (ht : PermutationSubgroupTransitive K) : ActionRegistryCovered actions K :=
  binary_character_registry_children C characters actions registry 0 checked K hle hindex ht

end SymmetricSubgroupAsymptotics.BinaryActionChildren8T26
