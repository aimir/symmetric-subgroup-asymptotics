import SymmetricSubgroupAsymptotics.CFSGGTwoPositiveRootMatrices
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel

/-! The four higher literal positive root groups commute in characteristic
three. The constant linear/quadratic coefficient commutations are proved
over F3 and transported through the prime-ring map. No field elements are
enumerated and no quotient-fixed-point lifting is presumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoHigherPositiveCommutation
open CFSGGTwoSerreMatrices CFSGGTwoPositiveDirections CFSGGTwoPositiveRootMatrices

def higherIndex (i : Fin 4) : Fin 6 := ⟨i.val+2,by omega⟩

private theorem prime_linear (i j : Fin 4) :
    Commute (positiveLinear (ZMod 3) (higherIndex i))
      (positiveLinear (ZMod 3) (higherIndex j)) := by
  change _ * _ = _ * _
  fin_cases i <;> fin_cases j <;> decide +kernel

private theorem prime_mixed (i j : Fin 4) :
    Commute (positiveLinear (ZMod 3) (higherIndex i))
      (positiveQuadratic (ZMod 3) (higherIndex j)) := by
  change _ * _ = _ * _
  fin_cases i <;> fin_cases j <;> decide +kernel

private theorem prime_quadratic (i j : Fin 4) :
    Commute (positiveQuadratic (ZMod 3) (higherIndex i))
      (positiveQuadratic (ZMod 3) (higherIndex j)) := by
  change _ * _ = _ * _
  fin_cases i <;> fin_cases j <;> decide +kernel

private theorem map_commute {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (X Y : Mat R) (h : Commute X Y) :
    Commute (f.mapMatrix X) (f.mapMatrix Y) := by
  change f.mapMatrix X*f.mapMatrix Y=f.mapMatrix Y*f.mapMatrix X
  rw [←map_mul,←map_mul,h.eq]

variable (R : Type*) [CommRing R] [CharP R 3]

theorem higher_linear_commute (i j : Fin 4) :
    Commute (positiveLinear R (higherIndex i)) (positiveLinear R (higherIndex j)) := by
  let f : ZMod 3 →+* R := ZMod.castHom (dvd_refl 3) R
  have h := map_commute f _ _ (prime_linear i j)
  simpa only [map_positiveLinear] using h

theorem higher_mixed_commute (i j : Fin 4) :
    Commute (positiveLinear R (higherIndex i)) (positiveQuadratic R (higherIndex j)) := by
  let f : ZMod 3 →+* R := ZMod.castHom (dvd_refl 3) R
  have h := map_commute f _ _ (prime_mixed i j)
  simpa only [map_positiveLinear,map_positiveQuadratic] using h

theorem higher_quadratic_commute (i j : Fin 4) :
    Commute (positiveQuadratic R (higherIndex i)) (positiveQuadratic R (higherIndex j)) := by
  let f : ZMod 3 →+* R := ZMod.castHom (dvd_refl 3) R
  have h := map_commute f _ _ (prime_quadratic i j)
  simpa only [map_positiveQuadratic] using h

private theorem quadratic_polynomials_commute
    {S B : Type*} [CommRing S] [Ring B] [Algebra S B]
    (E D F Q : B) (hEF : Commute E F) (hEQ : Commute E Q)
    (hDF : Commute D F) (hDQ : Commute D Q) (a b : S) :
    Commute (1+a • E+a^2 • D) (1+b • F+b^2 • Q) := by
  change _*_=_*_
  simp only [add_mul,mul_add,one_mul,mul_one,smul_mul_assoc,mul_smul_comm,
    smul_smul,smul_add,hEF.eq,hEQ.eq,hDF.eq,hDQ.eq,
    mul_comm a b,mul_comm a (b^2),mul_comm (a^2) b,mul_comm (a^2) (b^2)]
  abel

theorem polynomial_higher_commute (i j : Fin 4) (a b : R) :
    Commute (polynomialRoot R (higherIndex i) a) (polynomialRoot R (higherIndex j) b) :=
  quadratic_polynomials_commute _ _ _ _ (higher_linear_commute R i j)
    (higher_mixed_commute R i j) (higher_mixed_commute R j i).symm
    (higher_quadratic_commute R i j) a b

theorem positive_higher_commute (K : Type) [Field K] [CharP K 3]
    (i j : Fin 4) (a b : K) :
    Commute (positiveRoot K (higherIndex i) a) (positiveRoot K (higherIndex j) b) := by
  change _*_=_*_
  apply Units.ext
  simp only [Units.val_mul,positiveRoot_val]
  exact (polynomial_higher_commute K i j a b).eq

end SymmetricSubgroupAsymptotics.CFSGGTwoHigherPositiveCommutation
