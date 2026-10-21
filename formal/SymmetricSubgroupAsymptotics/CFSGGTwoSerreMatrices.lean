import SymmetricSubgroupAsymptotics.CFSGOrthogonalDSerreMatrices
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-! The literal triality-folded D4 matrices, with the pinned G₂ node order.
Node zero is the sum of the three mutually orthogonal outer D4 roots;
node one is the central D4 root. The first node is quadratic, not square zero. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGGTwoSerreMatrices
variable (R : Type*) [CommRing R]
abbrev Index := CFSGOrthogonalDSerreMatrices.Index 4
abbrev Mat := Matrix Index Index R
abbrev pos (i : Fin 4) : Index := Sum.inl i
abbrev neg (i : Fin 4) : Index := Sum.inr i

def outerPositive : Mat R :=
  CFSGOrthogonalDSerreMatrices.positive R 4 0 +
    CFSGOrthogonalDSerreMatrices.positive R 4 2 +
      CFSGOrthogonalDSerreMatrices.positive R 4 3

def positive (i : Fin 2) : Mat R :=
  if i=0 then outerPositive R else CFSGOrthogonalDSerreMatrices.positive R 4 1

def negative (i : Fin 2) : Mat R := (positive R i).transpose

def cartan (i : Fin 2) : Mat R :=
  if i=0 then CFSGOrthogonalDSerreMatrices.cartan R 4 0 +
    CFSGOrthogonalDSerreMatrices.cartan R 4 2 +
      CFSGOrthogonalDSerreMatrices.cartan R 4 3
  else CFSGOrthogonalDSerreMatrices.cartan R 4 1

def positiveSecond (i : Fin 2) : Mat R :=
  if i=0 then Matrix.single (pos 2) (neg 2) (-1) else 0

def negativeSecond (i : Fin 2) : Mat R := (positiveSecond R i).transpose

@[simp] theorem positive_zero : positive R 0=outerPositive R := if_pos rfl
@[simp] theorem positive_one :
    positive R 1=CFSGOrthogonalDSerreMatrices.positive R 4 1 := if_neg (by decide)

 theorem positive_zero_explicit : positive R 0=
    (Matrix.single (pos 0) (pos 1) 1-Matrix.single (neg 1) (neg 0) 1)+
    (Matrix.single (pos 2) (pos 3) 1-Matrix.single (neg 3) (neg 2) 1)+
    (Matrix.single (pos 2) (neg 3) 1-Matrix.single (pos 3) (neg 2) 1) := by
  simp [positive,outerPositive,CFSGOrthogonalDSerreMatrices.positive,
    CFSGOrthogonalDSerreMatrices.previous,pos,neg]

 theorem positive_one_explicit : positive R 1=
    Matrix.single (pos 1) (pos 2) 1-Matrix.single (neg 2) (neg 1) 1 := by
  simp [positive,CFSGOrthogonalDSerreMatrices.positive,pos,neg]

 theorem positive_square (i : Fin 2) :
    positive R i*positive R i=positiveSecond R i+positiveSecond R i := by
  fin_cases i
  · change positive R 0*positive R 0=positiveSecond R 0+positiveSecond R 0
    rw [positive_zero_explicit]
    simp only [positiveSecond,if_pos rfl,add_mul,mul_add,sub_mul,mul_sub]
    simp [pos,neg] <;> (ext a b; simp [Matrix.single]; split_ifs <;> ring)
  · change positive R 1*positive R 1=positiveSecond R 1+positiveSecond R 1
    rw [positive_one_explicit]
    simp [positiveSecond,pos,neg,sub_mul,mul_sub]

 theorem positive_mul_second (i : Fin 2) : positive R i*positiveSecond R i=0 := by
  fin_cases i
  · change positive R 0*positiveSecond R 0=0
    rw [positive_zero_explicit]
    simp [positiveSecond,pos,neg,add_mul,sub_mul]
  · simp [positiveSecond]

 theorem second_mul_positive (i : Fin 2) : positiveSecond R i*positive R i=0 := by
  fin_cases i
  · change positiveSecond R 0*positive R 0=0
    rw [positive_zero_explicit]
    simp [positiveSecond,pos,neg,mul_add,mul_sub]
  · simp [positiveSecond]

 theorem positiveSecond_sq_zero (i : Fin 2) : positiveSecond R i*positiveSecond R i=0 := by
  fin_cases i <;> simp [positiveSecond,pos,neg]

 theorem negative_square (i : Fin 2) :
    negative R i*negative R i=negativeSecond R i+negativeSecond R i := by
  simpa only [negative,negativeSecond,Matrix.transpose_mul,Matrix.transpose_add] using
    congrArg Matrix.transpose (positive_square R i)

 theorem negative_mul_second (i : Fin 2) : negative R i*negativeSecond R i=0 := by
  simpa only [negative,negativeSecond,Matrix.transpose_mul,Matrix.transpose_zero] using
    congrArg Matrix.transpose (second_mul_positive R i)

 theorem second_mul_negative (i : Fin 2) : negativeSecond R i*negative R i=0 := by
  simpa only [negative,negativeSecond,Matrix.transpose_mul,Matrix.transpose_zero] using
    congrArg Matrix.transpose (positive_mul_second R i)

 theorem negativeSecond_sq_zero (i : Fin 2) : negativeSecond R i*negativeSecond R i=0 := by
  simpa only [negativeSecond,Matrix.transpose_mul,Matrix.transpose_zero] using
    congrArg Matrix.transpose (positiveSecond_sq_zero R i)

 theorem positive_cube (i : Fin 2) : positive R i^3=0 := by
  rw [pow_succ,pow_two,positive_square,add_mul,second_mul_positive,zero_add]

 theorem negative_cube (i : Fin 2) : negative R i^3=0 := by
  rw [pow_succ,pow_two,negative_square,add_mul,second_mul_negative,zero_add]

 theorem map_positive {S : Type*} [CommRing S] (f : R→+*S) (i : Fin 2) :
    f.mapMatrix (positive R i)=positive S i := by
  by_cases h : i=0
  · simp only [positive,if_pos h,outerPositive]
    rw [map_add,map_add,CFSGOrthogonalDSerreMatrices.map_positive,
      CFSGOrthogonalDSerreMatrices.map_positive,CFSGOrthogonalDSerreMatrices.map_positive]
  · simp only [positive,if_neg h]
    exact CFSGOrthogonalDSerreMatrices.map_positive R 4 f 1

 theorem map_negative {S : Type*} [CommRing S] (f : R→+*S) (i : Fin 2) :
    f.mapMatrix (negative R i)=negative S i := by
  change (positive R i).transpose.map f=(positive S i).transpose
  rw [Matrix.transpose_map]
  exact congrArg Matrix.transpose (map_positive R f i)

 theorem map_cartan {S : Type*} [CommRing S] (f : R→+*S) (i : Fin 2) :
    f.mapMatrix (cartan R i)=cartan S i := by
  by_cases h : i=0
  · simp only [cartan,if_pos h]
    rw [map_add,map_add,CFSGOrthogonalDSerreMatrices.map_cartan,
      CFSGOrthogonalDSerreMatrices.map_cartan,CFSGOrthogonalDSerreMatrices.map_cartan]
  · simp only [cartan,if_neg h]
    exact CFSGOrthogonalDSerreMatrices.map_cartan R 4 f 1

end SymmetricSubgroupAsymptotics.CFSGGTwoSerreMatrices
