import SymmetricSubgroupAsymptotics.LiteralPolynomialSpanWitnessCoordinateTransport
import SymmetricSubgroupAsymptotics.BinaryBitmaskCoordinates

/-! The norm of an eleven-cycle with one fixed point projects onto its
two constant coordinates. Compressing a mover that displaces the fixed
point exchanges those constants. On the ten-dimensional augmentation,
1+a² is cyclic. The combined operator EbE+1+a² has the displayed cyclic
polynomial chain on twelve coordinates. The polynomial/PID theorem then
bounds every actual invariant subspace by one generator. -/

set_option autoImplicit false
noncomputable section
open scoped MonoidAlgebra BigOperators

namespace SymmetricSubgroupAsymptotics.BinaryElevenCyclePolynomial

def columnMask : Fin 12 → ℕ :=
  ![2053, 2058, 2068, 2088, 2128, 2208, 2368, 2688, 3328, 2561, 3074, 2047]

def operator : Module.End (ZMod 2) (Fin 12 → ZMod 2) :=
  (binaryMatrixOfColumnMasks 12 columnMask).mulVecLin

def vectorMask : Fin 12 → ℕ :=
  ![1, 2053, 2030, 2133, 1790, 3333, 1772, 3423, 2014, 2213, 1486, 2804]
def vectors (_ : Fin 1) (m : Fin 12) : Fin 12 → ZMod 2 :=
  binaryVectorOfMask 12 (vectorMask m)
def coefficientMask : Fin 12 → ℕ :=
  ![1, 3931, 1924, 4081, 3851, 3599, 3841, 3085, 3871, 2571, 3901, 1927]
def coefficient (i : Fin 12) : Fin 12 → ZMod 2 :=
  binaryVectorOfMask 12 (coefficientMask i)

def polynomialWitness : LiteralPolynomialSpanWitness operator 1 11 where
  vectors := vectors
  step j m := by
    funext x
    revert j m x
    decide +kernel
  selected i := (0, i)
  coefficient := coefficient
  point_eq := by decide +kernel

variable {G : Type} [Group G]

def averagingOperator (rho : Representation (ZMod 2) G (Fin 12 → ZMod 2)) (a : G) :
    Module.End (ZMod 2) (Fin 12 → ZMod 2) :=
  ∑ i : Fin 11, rho a ^ i.val

def actualOperator (rho : Representation (ZMod 2) G (Fin 12 → ZMod 2)) (a b : G) :
    Module.End (ZMod 2) (Fin 12 → ZMod 2) :=
  averagingOperator rho a * rho b * averagingOperator rho a + 1 + rho a ^ 2

def averagingElement (a : G) : (ZMod 2)[G] :=
  ∑ i : Fin 11, MonoidAlgebra.single a 1 ^ i.val

def algebraElement (a b : G) : (ZMod 2)[G] :=
  averagingElement a * MonoidAlgebra.single b 1 * averagingElement a + 1 +
    MonoidAlgebra.single a 1 ^ 2

theorem actualOperator_eq (rho : Representation (ZMod 2) G (Fin 12 → ZMod 2)) (a b : G) :
    actualOperator rho a b = rho.asAlgebraHom (algebraElement a b) := by
  simp only [actualOperator, averagingOperator, algebraElement, averagingElement,
    map_add, map_mul, map_sum, map_pow, map_one,
    Representation.asAlgebraHom_single, one_smul]

theorem uniform_of_basis (rho : Representation (ZMod 2) G (Fin 12 → ZMod 2)) (a b : G)
    (e : Equiv.Perm (Fin 12))
    (h : ∀ i x : Fin 12,
      actualOperator rho a b
        (fun y ↦ (Pi.single i 1 : Fin 12 → ZMod 2) (e.symm y)) x =
          operator (Pi.single i 1) (e.symm x)) :
    UniformSubrepresentationGeneratorBound rho 1 :=
  polynomialWitness.uniform_of_reindexed_basis rho (algebraElement a b)
    (actualOperator rho a b) (actualOperator_eq rho a b) e h

end SymmetricSubgroupAsymptotics.BinaryElevenCyclePolynomial

end
