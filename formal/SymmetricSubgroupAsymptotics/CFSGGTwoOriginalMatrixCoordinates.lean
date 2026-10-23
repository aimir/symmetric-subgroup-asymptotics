import SymmetricSubgroupAsymptotics.CFSGGTwoOriginalBasisMatrices
import Mathlib.Tactic.NormNum

/-! Integral unit-pivot coordinates on the fourteen original G2 vector
images. The coordinate table has no divisions and works over every
commutative coefficient ring, including characteristics two and three. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics.CFSGGTwoOriginalMatrixCoordinates
open CFSGGTwoSerreMatrices CFSGGTwoOriginalBasisMatrixPilot
open CFSGGTwoOriginalBasisMatrices
variable (R : Type*) [CommRing R]

abbrev BasisIndex := CFSGGTwoOriginalFourteenFamily.Index

def positiveMatrices (i : Fin 6) : Mat R :=
  match i.val with
  | 0 => positive R 0
  | 1 => positive R 1
  | 2 => firstMatrix R
  | 3 => secondMatrix R
  | 4 => thirdMatrix R
  | _ => highestMatrix R

def negativeMatrices (i : Fin 6) : Mat R :=
  match i.val with
  | 0 => negative R 0
  | 1 => negative R 1
  | 2 => -(firstMatrix R).transpose
  | 3 => (secondMatrix R).transpose
  | 4 => -(thirdMatrix R).transpose
  | _ => (highestMatrix R).transpose

def matrixVectors : BasisIndex → Mat R :=
  Sum.elim (fun z => if z.1 then negativeMatrices R z.2 else positiveMatrices R z.2) (cartan R)

def matrixCoordinates : Mat R →ₗ[R] (BasisIndex → R) where
  toFun M := Sum.elim (fun z => if z.1 then
    match z.2.val with
    | 0 => M (pos 1) (pos 0)
    | 1 => M (pos 2) (pos 1)
    | 2 => -M (pos 2) (pos 0)
    | 3 => -M (pos 3) (pos 0)
    | 4 => -M (neg 0) (pos 2)
    | _ => M (neg 0) (pos 1)
    else match z.2.val with
    | 0 => M (pos 0) (pos 1)
    | 1 => M (pos 1) (pos 2)
    | 2 => M (pos 0) (pos 2)
    | 3 => -M (pos 0) (pos 3)
    | 4 => -M (pos 0) (neg 2)
    | _ => -M (pos 0) (neg 1))
    (fun i => if i=0 then M (pos 0) (pos 0) else M (pos 1) (pos 1)+M (pos 0) (pos 0))
  map_add' M N := by
    funext i
    cases i with
    | inl z =>
      obtain ⟨b,j⟩ := z
      cases b <;> fin_cases j <;> simp [Matrix.add_apply,add_comm,add_assoc]
    | inr j => fin_cases j <;> simp [Matrix.add_apply,add_comm,add_left_comm,add_assoc]
  map_smul' a M := by
    funext i
    cases i with
    | inl z =>
      obtain ⟨b,j⟩ := z
      cases b <;> fin_cases j <;> simp [Matrix.smul_apply,smul_eq_mul]
    | inr j => fin_cases j <;> simp [Matrix.smul_apply,smul_eq_mul,mul_add]

private theorem map_single_one {S : Type*} [CommRing S] (f : R →+* S)
    (i j : CFSGGTwoSerreMatrices.Index) :
    f.mapMatrix (Matrix.single i j (1:R))=Matrix.single i j (1:S) := by
  change (Matrix.single i j (1:R)).map f=Matrix.single i j (1:S)
  simp only [Matrix.map_single,map_one]

private theorem map_transpose {S : Type*} [CommRing S] (f : R →+* S) (M : Mat R) :
    f.mapMatrix M.transpose=(f.mapMatrix M).transpose := rfl

private theorem map_first {S : Type*} [CommRing S] (f : R →+* S) :
    f.mapMatrix (firstMatrix R)=firstMatrix S := by
  simp only [firstMatrix,map_add,map_sub,map_single_one]

private theorem map_second {S : Type*} [CommRing S] (f : R →+* S) :
    f.mapMatrix (secondMatrix R)=secondMatrix S := by
  simp only [secondMatrix,map_add,map_sub,map_neg,map_single_one]

private theorem map_third {S : Type*} [CommRing S] (f : R →+* S) :
    f.mapMatrix (thirdMatrix R)=thirdMatrix S := by
  simp only [thirdMatrix,map_add,map_neg,map_single_one]

private theorem map_highest {S : Type*} [CommRing S] (f : R →+* S) :
    f.mapMatrix (highestMatrix R)=highestMatrix S := by
  simp only [highestMatrix,map_add,map_neg,map_single_one]

theorem map_matrixVectors {S : Type*} [CommRing S] (f : R →+* S) (j : BasisIndex) :
    f.mapMatrix (matrixVectors R j)=matrixVectors S j := by
  cases j with
  | inl z =>
    obtain ⟨b,k⟩ := z
    cases b
    · fin_cases k
      · exact map_positive R f 0
      · exact map_positive R f 1
      · exact map_first R f
      · exact map_second R f
      · exact map_third R f
      · exact map_highest R f
    · fin_cases k
      · exact map_negative R f 0
      · exact map_negative R f 1
      · change f.mapMatrix (-(firstMatrix R).transpose)=-(firstMatrix S).transpose
        rw [map_neg,map_transpose,map_first]
      · change f.mapMatrix ((secondMatrix R).transpose)=(secondMatrix S).transpose
        rw [map_transpose,map_second]
      · change f.mapMatrix (-(thirdMatrix R).transpose)=-(thirdMatrix S).transpose
        rw [map_neg,map_transpose,map_third]
      · change f.mapMatrix ((highestMatrix R).transpose)=(highestMatrix S).transpose
        rw [map_transpose,map_highest]
  | inr k => exact map_cartan R f k

theorem coordinates_map {S : Type*} [CommRing S] (f : R →+* S) (M : Mat R) :
    matrixCoordinates S (f.mapMatrix M)=fun i => f (matrixCoordinates R M i) := by
  funext i
  cases i with
  | inl z =>
    obtain ⟨b,k⟩ := z
    cases b <;> fin_cases k <;> simp [matrixCoordinates]
  | inr k => fin_cases k <;> simp [matrixCoordinates]


private theorem integer_coordinates_positive_0 :
    matrixCoordinates ℤ (positiveMatrices ℤ 0)=Pi.single (Sum.inl (false,(0 : Fin 6))) 1 := by
  decide +kernel

private theorem integer_coordinates_positive_1 :
    matrixCoordinates ℤ (positiveMatrices ℤ 1)=Pi.single (Sum.inl (false,(1 : Fin 6))) 1 := by
  decide +kernel

private theorem integer_coordinates_positive_2 :
    matrixCoordinates ℤ (positiveMatrices ℤ 2)=Pi.single (Sum.inl (false,(2 : Fin 6))) 1 := by
  decide +kernel

private theorem integer_coordinates_positive_3 :
    matrixCoordinates ℤ (positiveMatrices ℤ 3)=Pi.single (Sum.inl (false,(3 : Fin 6))) 1 := by
  decide +kernel

private theorem integer_coordinates_positive_4 :
    matrixCoordinates ℤ (positiveMatrices ℤ 4)=Pi.single (Sum.inl (false,(4 : Fin 6))) 1 := by
  decide +kernel

private theorem integer_coordinates_positive_5 :
    matrixCoordinates ℤ (positiveMatrices ℤ 5)=Pi.single (Sum.inl (false,(5 : Fin 6))) 1 := by
  decide +kernel

private theorem integer_coordinates_negative_0 :
    matrixCoordinates ℤ (negativeMatrices ℤ 0)=Pi.single (Sum.inl (true,(0 : Fin 6))) 1 := by
  decide +kernel

private theorem integer_coordinates_negative_1 :
    matrixCoordinates ℤ (negativeMatrices ℤ 1)=Pi.single (Sum.inl (true,(1 : Fin 6))) 1 := by
  decide +kernel

private theorem integer_coordinates_negative_2 :
    matrixCoordinates ℤ (negativeMatrices ℤ 2)=Pi.single (Sum.inl (true,(2 : Fin 6))) 1 := by
  decide +kernel

private theorem integer_coordinates_negative_3 :
    matrixCoordinates ℤ (negativeMatrices ℤ 3)=Pi.single (Sum.inl (true,(3 : Fin 6))) 1 := by
  decide +kernel

private theorem integer_coordinates_negative_4 :
    matrixCoordinates ℤ (negativeMatrices ℤ 4)=Pi.single (Sum.inl (true,(4 : Fin 6))) 1 := by
  decide +kernel

private theorem integer_coordinates_negative_5 :
    matrixCoordinates ℤ (negativeMatrices ℤ 5)=Pi.single (Sum.inl (true,(5 : Fin 6))) 1 := by
  decide +kernel

private theorem integer_coordinates_cartan_0 :
    matrixCoordinates ℤ (cartan ℤ 0)=Pi.single (Sum.inr (0 : Fin 2)) 1 := by
  decide +kernel

private theorem integer_coordinates_cartan_1 :
    matrixCoordinates ℤ (cartan ℤ 1)=Pi.single (Sum.inr (1 : Fin 2)) 1 := by
  decide +kernel

theorem integer_coordinates_vector (j : BasisIndex) :
    matrixCoordinates ℤ (matrixVectors ℤ j)=Pi.single j 1 := by
  cases j with
  | inl z =>
    obtain ⟨b,k⟩ := z
    cases b
    · fin_cases k
      · exact integer_coordinates_positive_0
      · exact integer_coordinates_positive_1
      · exact integer_coordinates_positive_2
      · exact integer_coordinates_positive_3
      · exact integer_coordinates_positive_4
      · exact integer_coordinates_positive_5
    · fin_cases k
      · exact integer_coordinates_negative_0
      · exact integer_coordinates_negative_1
      · exact integer_coordinates_negative_2
      · exact integer_coordinates_negative_3
      · exact integer_coordinates_negative_4
      · exact integer_coordinates_negative_5
  | inr k =>
    fin_cases k
    · exact integer_coordinates_cartan_0
    · exact integer_coordinates_cartan_1

theorem coordinates_vector (j : BasisIndex) :
    matrixCoordinates R (matrixVectors R j)=Pi.single j 1 := by
  have h := coordinates_map ℤ (Int.castRingHom R) (matrixVectors ℤ j)
  rw [map_matrixVectors,integer_coordinates_vector] at h
  refine h.trans ?_
  funext i
  by_cases hi : i=j <;> simp [Pi.single_apply,hi]

theorem coordinates_positive (j : Fin 6) :
    matrixCoordinates R (positiveMatrices R j)=Pi.single (Sum.inl (false,j)) 1 :=
  coordinates_vector R (Sum.inl (false,j))

theorem coordinates_negative (j : Fin 6) :
    matrixCoordinates R (negativeMatrices R j)=Pi.single (Sum.inl (true,j)) 1 :=
  coordinates_vector R (Sum.inl (true,j))

theorem coordinates_cartan (j : Fin 2) :
    matrixCoordinates R (cartan R j)=Pi.single (Sum.inr j) 1 :=
  coordinates_vector R (Sum.inr j)

def matrixCombination : (BasisIndex → R) →ₗ[R] Mat R :=
  Fintype.linearCombination R (matrixVectors R)

theorem coordinates_combination (a : BasisIndex → R) :
    matrixCoordinates R (matrixCombination R a)=a := by
  classical
  change matrixCoordinates R (∑ i,a i • matrixVectors R i)=a
  rw [map_sum]
  simp only [map_smul,coordinates_vector]
  funext j
  simp [Finset.sum_apply,Pi.single_apply,smul_eq_mul]

theorem matrixCombination_injective : Function.Injective (matrixCombination R) := by
  intro a b h
  have hh := congrArg (matrixCoordinates R) h
  simpa only [coordinates_combination] using hh

end SymmetricSubgroupAsymptotics.CFSGGTwoOriginalMatrixCoordinates
