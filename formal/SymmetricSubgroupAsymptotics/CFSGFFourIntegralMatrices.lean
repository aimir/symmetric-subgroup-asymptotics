import SymmetricSubgroupAsymptotics.CFSGFFourQuadraticPositive
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckIntegralQuadratic

/-! Literal integral lifts of the folded E6 H/E/F matrices and of their
quadratic coefficients. The negative coefficient uses actual integral
Geck opposition, so no denominators enter the source lattice. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFFourSerreMatrices
open CFSGNormTwoRootPairing CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
local instance fFourIntegralMatricesDecEq : DecidableEq (Roots CartanMatrix.E₆) := Classical.decEq _
abbrev IntMat := Matrix Index Index ℤ

def e6HZ (i : Fin 6) : IntMat := CFSGGeckIntegralMatrices.H E6Base (E6Index i)
def e6EZ (i : Fin 6) : IntMat := CFSGGeckIntegralMatrices.E E6Base (E6Index i)
def e6FZ (i : Fin 6) : IntMat := CFSGGeckIntegralMatrices.F E6Base (E6Index i)
def e6SecondZ (i : Fin 6) : IntMat :=
  CFSGNormTwoGeckIntegralQuadratic.positiveSecond CartanMatrix.E₆ CartanMatrix.E₆_transpose
    E6_positive_definite E6Base (E6Index i)

def integerH (i : Fin 4) : IntMat := ![e6HZ 0+e6HZ 5,e6HZ 2+e6HZ 4,e6HZ 3,e6HZ 1] i
def integerE (i : Fin 4) : IntMat := ![e6EZ 0+e6EZ 5,e6EZ 2+e6EZ 4,e6EZ 3,e6EZ 1] i
def integerF (i : Fin 4) : IntMat := ![e6FZ 0+e6FZ 5,e6FZ 2+e6FZ 4,e6FZ 3,e6FZ 1] i

def positiveSecondZ (i : Fin 4) : IntMat :=
  ![e6SecondZ 0+e6SecondZ 5+e6EZ 0*e6EZ 5,
    e6SecondZ 2+e6SecondZ 4+e6EZ 2*e6EZ 4,e6SecondZ 3,e6SecondZ 1] i

def negativeSecond (i : Fin 4) : Mat :=
  CFSGGeckOppositionAlgEquiv.opposition E6Base (positiveSecond i)
def negativeSecondZ (i : Fin 4) : IntMat :=
  CFSGGeckIntegralMatrices.Omega E6Base*positiveSecondZ i*CFSGGeckIntegralMatrices.Omega E6Base

@[simp] theorem map_e6HZ (i : Fin 6) : (Int.castRingHom ℚ).mapMatrix (e6HZ i)=e6H i :=
  CFSGGeckIntegralMatrices.map_H E6Base (E6Index i)
@[simp] theorem map_e6EZ (i : Fin 6) : (Int.castRingHom ℚ).mapMatrix (e6EZ i)=e6E i :=
  CFSGGeckIntegralMatrices.map_E E6Base (E6Index i)
@[simp] theorem map_e6FZ (i : Fin 6) : (Int.castRingHom ℚ).mapMatrix (e6FZ i)=e6F i :=
  CFSGGeckIntegralMatrices.map_F E6Base (E6Index i)
@[simp] theorem map_e6SecondZ (i : Fin 6) :
    (Int.castRingHom ℚ).mapMatrix (e6SecondZ i)=e6Second i :=
  CFSGNormTwoGeckIntegralQuadratic.map_positiveSecond CartanMatrix.E₆
    CartanMatrix.E₆_transpose E6_positive_definite E6Base (E6Index i)

@[simp] theorem map_integerH (i : Fin 4) : (Int.castRingHom ℚ).mapMatrix (integerH i)=cartan i := by
  fin_cases i
  · change (Int.castRingHom ℚ).mapMatrix (e6HZ 0+e6HZ 5)=e6H 0+e6H 5
    rw [map_add,map_e6HZ,map_e6HZ]
  · change (Int.castRingHom ℚ).mapMatrix (e6HZ 2+e6HZ 4)=e6H 2+e6H 4
    rw [map_add,map_e6HZ,map_e6HZ]
  · exact map_e6HZ 3
  · exact map_e6HZ 1
@[simp] theorem map_integerE (i : Fin 4) : (Int.castRingHom ℚ).mapMatrix (integerE i)=positive i := by
  fin_cases i
  · change (Int.castRingHom ℚ).mapMatrix (e6EZ 0+e6EZ 5)=e6E 0+e6E 5
    rw [map_add,map_e6EZ,map_e6EZ]
  · change (Int.castRingHom ℚ).mapMatrix (e6EZ 2+e6EZ 4)=e6E 2+e6E 4
    rw [map_add,map_e6EZ,map_e6EZ]
  · exact map_e6EZ 3
  · exact map_e6EZ 1
@[simp] theorem map_integerF (i : Fin 4) : (Int.castRingHom ℚ).mapMatrix (integerF i)=negative i := by
  fin_cases i
  · change (Int.castRingHom ℚ).mapMatrix (e6FZ 0+e6FZ 5)=e6F 0+e6F 5
    rw [map_add,map_e6FZ,map_e6FZ]
  · change (Int.castRingHom ℚ).mapMatrix (e6FZ 2+e6FZ 4)=e6F 2+e6F 4
    rw [map_add,map_e6FZ,map_e6FZ]
  · exact map_e6FZ 3
  · exact map_e6FZ 1
@[simp] theorem map_positiveSecondZ (i : Fin 4) :
    (Int.castRingHom ℚ).mapMatrix (positiveSecondZ i)=positiveSecond i := by
  fin_cases i
  · change (Int.castRingHom ℚ).mapMatrix (e6SecondZ 0+e6SecondZ 5+e6EZ 0*e6EZ 5)=
      e6Second 0+e6Second 5+e6E 0*e6E 5
    rw [map_add,map_add,map_mul,map_e6SecondZ,map_e6SecondZ,map_e6EZ,map_e6EZ]
  · change (Int.castRingHom ℚ).mapMatrix (e6SecondZ 2+e6SecondZ 4+e6EZ 2*e6EZ 4)=
      e6Second 2+e6Second 4+e6E 2*e6E 4
    rw [map_add,map_add,map_mul,map_e6SecondZ,map_e6SecondZ,map_e6EZ,map_e6EZ]
  · exact map_e6SecondZ 3
  · exact map_e6SecondZ 1
@[simp] theorem map_negativeSecondZ (i : Fin 4) :
    (Int.castRingHom ℚ).mapMatrix (negativeSecondZ i)=negativeSecond i := by
  rw [negativeSecondZ,CFSGGeckIntegralMatrices.map_opposition,map_positiveSecondZ]
  rfl

theorem opposition_positive (i : Fin 4) :
    CFSGGeckOppositionAlgEquiv.opposition E6Base (positive i)=negative i := by
  have hh (j : Fin 6) : CFSGGeckOppositionAlgEquiv.opposition E6Base (e6E j)=e6F j :=
    CFSGGeckOppositionAlgEquiv.opposition_E E6Base (E6Index j)
  fin_cases i <;> simp [positive,negative,map_add,hh]

theorem negative_quadratic (i : Fin 4) :
    negative i*negative i=negativeSecond i+negativeSecond i ∧
      negative i*negativeSecond i=0 ∧ negativeSecond i*negative i=0 ∧
      negativeSecond i*negativeSecond i=0 := by
  obtain ⟨hs,hl,hr,hd⟩ := positive_quadratic i
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [map_mul,map_add,opposition_positive,negativeSecond] using
      congrArg (CFSGGeckOppositionAlgEquiv.opposition E6Base) hs
  · simpa only [map_mul,map_zero,opposition_positive,negativeSecond] using
      congrArg (CFSGGeckOppositionAlgEquiv.opposition E6Base) hl
  · simpa only [map_mul,map_zero,opposition_positive,negativeSecond] using
      congrArg (CFSGGeckOppositionAlgEquiv.opposition E6Base) hr
  · simpa only [map_mul,map_zero,negativeSecond] using
      congrArg (CFSGGeckOppositionAlgEquiv.opposition E6Base) hd

end SymmetricSubgroupAsymptotics.CFSGFFourSerreMatrices
