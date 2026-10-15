import SymmetricSubgroupAsymptotics.LiteralPolynomialSpanWitnessCoordinateTransport
import SymmetricSubgroupAsymptotics.BinaryBitmaskCoordinates

/-! A paired five-cycle and a central flip give an eight-dimensional
augmentation block. The five-cycle norm E projects onto four constants.
The operator (1+E)(t+k)+EbE combines a cyclic augmentation operator with
the compressed action of a mover on constants. Its displayed polynomial
chain spans all twelve coordinates, so every actual invariant subspace
has one generator by the polynomial/PID theorem. -/

set_option autoImplicit false
noncomputable section
open scoped MonoidAlgebra BigOperators

namespace SymmetricSubgroupAsymptotics.BinaryPairedFiveCycleCentralFlipPolynomial

def columnMask : Fin 12 → ℕ :=
  ![1364, 2035, 4076, 1999, 4022, 1855, 3806, 1279, 2942, 1021, 3578, 682]

def operator : Module.End (ZMod 2) (Fin 12 → ZMod 2) :=
  (binaryMatrixOfColumnMasks 12 columnMask).mulVecLin

def vectorMask : Fin 12 → ℕ :=
  ![2, 2035, 1398, 2252, 168, 1039, 1918, 3326, 552, 781, 1524, 3008]
def vectors (_ : Fin 1) (m : Fin 12) : Fin 12 → ZMod 2 :=
  binaryVectorOfMask 12 (vectorMask m)
def coefficientMask : Fin 12 → ℕ :=
  ![2568, 1, 2846, 1361, 1451, 324, 2240, 1029, 850, 1301, 1126, 642]
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

def actualOperator (rho : Representation (ZMod 2) G (Fin 12 → ZMod 2)) (t k b : G) :
    Module.End (ZMod 2) (Fin 12 → ZMod 2) :=
  let T := rho t
  let E := 1 + T + T ^ 2 + T ^ 3 + T ^ 4
  (1 + E) * (T + rho k) + E * rho b * E

def algebraElement (t k b : G) : (ZMod 2)[G] :=
  let T := MonoidAlgebra.single t 1
  let K := MonoidAlgebra.single k 1
  let B := MonoidAlgebra.single b 1
  let E := 1 + T + T ^ 2 + T ^ 3 + T ^ 4
  (1 + E) * (T + K) + E * B * E

theorem actualOperator_eq (rho : Representation (ZMod 2) G (Fin 12 → ZMod 2)) (t k b : G) :
    actualOperator rho t k b = rho.asAlgebraHom (algebraElement t k b) := by
  simp only [actualOperator, algebraElement, map_add, map_mul, map_pow, map_one,
    Representation.asAlgebraHom_single, one_smul]

theorem uniform_of_basis (rho : Representation (ZMod 2) G (Fin 12 → ZMod 2)) (t k b : G)
    (e : Equiv.Perm (Fin 12))
    (h : ∀ i x : Fin 12,
      actualOperator rho t k b
        (fun y ↦ (Pi.single i 1 : Fin 12 → ZMod 2) (e.symm y)) x =
          operator (Pi.single i 1) (e.symm x)) :
    UniformSubrepresentationGeneratorBound rho 1 :=
  polynomialWitness.uniform_of_reindexed_basis rho (algebraElement t k b)
    (actualOperator rho t k b) (actualOperator_eq rho t k b) e h

end SymmetricSubgroupAsymptotics.BinaryPairedFiveCycleCentralFlipPolynomial

end
