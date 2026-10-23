import SymmetricSubgroupAsymptotics.CFSGGTwoPositiveDirections
import SymmetricSubgroupAsymptotics.CFSGGTwoExceptionalCoefficients

/-! Integral coefficient transport for the six literal positive Weyl
words. A selected higher-root pilot fixes the actual normalization before
collecting or fixed-U formulas are asserted. No field elements are
enumerated and no bad-prime positive-simple generation is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoPositiveWordCoordinates
open CFSGGTwoSerreMatrices CFSGGTwoShortWeylMatrices
open CFSGGTwoExceptionalCoefficients CFSGGTwoPositiveDirections
open CFSGGTwoOriginalMatrixCoordinates CFSGGTwoOriginalBasisMatrixPilot
variable (R : Type*) [CommRing R]

def directionUnit (j : Fin 6) : (Mat R)ˣ :=
  match j.val with
  | 0 => 1
  | 1 => 1
  | 2 => longWeyl R
  | 3 => shortWeyl R * longWeyl R
  | 4 => shortWeyl R
  | _ => longWeyl R * shortWeyl R

def linearDirection (j : Fin 6) : Mat R :=
  (directionUnit R j : Mat R) * positive R (rootNode j) *
    (↑((directionUnit R j)⁻¹) : Mat R)

def secondDirection (j : Fin 6) : Mat R :=
  (directionUnit R j : Mat R) * positiveSecond R (rootNode j) *
    (↑((directionUnit R j)⁻¹) : Mat R)

theorem map_scalar {S : Type*} [CommRing S] (f : R →+* S) (a : R) (M : Mat R) :
    f.mapMatrix (a • M)=f a • f.mapMatrix M := by
  apply Matrix.ext
  intro i j
  exact map_mul f a (M i j)

theorem map_rootUnit {S : Type*} [CommRing S] (f : R →+* S)
    (neg : Bool) (i : Fin 2) (t : R) :
    Units.map f.mapMatrix.toMonoidHom (rootTransvection R neg i t)=
      rootTransvection S neg i (f t) := by
  apply Units.ext
  change f.mapMatrix (1+t • rootMatrix R neg i+t^2 • rootSecond R neg i)=
    1+f t • rootMatrix S neg i+(f t)^2 • rootSecond S neg i
  rw [map_add,map_add,map_one,map_scalar,map_scalar,map_rootMatrix,map_rootSecond,map_pow]

theorem map_shortWeyl {S : Type*} [CommRing S] (f : R →+* S) :
    Units.map f.mapMatrix.toMonoidHom (shortWeyl R)=shortWeyl S := by
  simp only [shortWeyl,map_mul,map_rootUnit,map_one,map_neg]

theorem map_longWeyl {S : Type*} [CommRing S] (f : R →+* S) :
    Units.map f.mapMatrix.toMonoidHom (longWeyl R)=longWeyl S := by
  simp only [longWeyl,map_mul,map_rootUnit,map_one,map_neg]

theorem map_directionUnit {S : Type*} [CommRing S] (f : R →+* S) (j : Fin 6) :
    Units.map f.mapMatrix.toMonoidHom (directionUnit R j)=directionUnit S j := by
  fin_cases j <;> simp only [directionUnit,map_mul,map_one,map_shortWeyl,map_longWeyl]

theorem map_linearDirection {S : Type*} [CommRing S] (f : R →+* S) (j : Fin 6) :
    f.mapMatrix (linearDirection R j)=linearDirection S j := by
  have hg := congrArg (fun u : (Mat S)ˣ => (u : Mat S)) (map_directionUnit R f j)
  change f.mapMatrix (directionUnit R j : Mat R)=(directionUnit S j : Mat S) at hg
  have hi := congrArg (fun u : (Mat S)ˣ => (↑(u⁻¹) : Mat S)) (map_directionUnit R f j)
  change f.mapMatrix (↑((directionUnit R j)⁻¹) : Mat R)=
    (↑((directionUnit S j)⁻¹) : Mat S) at hi
  change f.mapMatrix ((directionUnit R j : Mat R) * positive R (rootNode j) *
      (↑((directionUnit R j)⁻¹) : Mat R))=_
  rw [map_mul,map_mul,hg,hi,map_positive]
  rfl

theorem map_secondDirection {S : Type*} [CommRing S] (f : R →+* S) (j : Fin 6) :
    f.mapMatrix (secondDirection R j)=secondDirection S j := by
  have hg := congrArg (fun u : (Mat S)ˣ => (u : Mat S)) (map_directionUnit R f j)
  change f.mapMatrix (directionUnit R j : Mat R)=(directionUnit S j : Mat S) at hg
  have hi := congrArg (fun u : (Mat S)ˣ => (↑(u⁻¹) : Mat S)) (map_directionUnit R f j)
  change f.mapMatrix (↑((directionUnit R j)⁻¹) : Mat R)=
    (↑((directionUnit S j)⁻¹) : Mat S) at hi
  change f.mapMatrix ((directionUnit R j : Mat R) * positiveSecond R (rootNode j) *
      (↑((directionUnit R j)⁻¹) : Mat R))=_
  rw [map_mul,map_mul,hg,hi,map_positiveSecond]
  rfl

private theorem integer_linear_two : linearDirection ℤ 2=firstMatrix ℤ := by
  decide +kernel

private theorem integer_second_two :
    secondDirection ℤ 2=Matrix.single (pos 1) (neg 1) (-1:ℤ) := by
  decide +kernel

theorem linear_two : linearDirection R 2=firstMatrix R := by
  let f : ℤ →+* R := Int.castRingHom R
  calc
    _=f.mapMatrix (linearDirection ℤ 2) := (map_linearDirection ℤ f 2).symm
    _=f.mapMatrix (firstMatrix ℤ) := congrArg f.mapMatrix integer_linear_two
    _=firstMatrix R := by
      change f.mapMatrix (matrixVectors ℤ (Sum.inl (false,2)))=
        matrixVectors R (Sum.inl (false,2))
      exact map_matrixVectors ℤ f _

theorem second_two : secondDirection R 2=Matrix.single (pos 1) (neg 1) (-1:R) := by
  let f : ℤ →+* R := Int.castRingHom R
  calc
    _=f.mapMatrix (secondDirection ℤ 2) := (map_secondDirection ℤ f 2).symm
    _=f.mapMatrix (Matrix.single (pos 1) (neg 1) (-1:ℤ)) :=
      congrArg f.mapMatrix integer_second_two
    _=_ := by
      change (Matrix.single (pos 1) (neg 1) (-1:ℤ)).map f=
        Matrix.single (pos 1) (neg 1) (-1:R)
      simp only [Matrix.map_single,map_neg,map_one]

theorem directionUnit_eq (K : Type) [Field K] (j : Fin 6) :
    directionUnit K j=directionWord K j := by
  fin_cases j <;> rfl

end SymmetricSubgroupAsymptotics.CFSGGTwoPositiveWordCoordinates
