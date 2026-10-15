import SymmetricSubgroupAsymptotics.LiteralPolynomialSpanWitnessCoordinateTransport
import SymmetricSubgroupAsymptotics.BinaryBitmaskCoordinates

/-! A paired ternary rotation and a central flip give a cyclic
four-dimensional binary augmentation fibre. A mover exchanges its two
transports and cycles the four ternary constants. Replacing the return
map on augmentation with t+k gives one cyclic twelve-dimensional operator.
The literal recurrence below certifies this shared construction, and the
polynomial/PID theorem bounds every actual invariant subspace. -/

set_option autoImplicit false
noncomputable section
open scoped MonoidAlgebra BigOperators

namespace SymmetricSubgroupAsymptotics.BinaryPairedTernaryCentralFlipPolynomial

def columnMask : Fin 12 → ℕ := ![32, 25, 2072, 4, 2, 2305, 2177, 1024, 512, 400, 392, 64]

def operator : Module.End (ZMod 2) (Fin 12 → ZMod 2) :=
  (binaryMatrixOfColumnMasks 12 columnMask).mulVecLin

def vectorMask : Fin 12 → ℕ := ![1, 32, 2305, 608, 16, 2, 25, 38, 256, 512, 400, 1538]
def vectors (_ : Fin 1) (m : Fin 12) : Fin 12 → ZMod 2 :=
  binaryVectorOfMask 12 (vectorMask m)
def coefficientMask : Fin 12 → ℕ := ![1, 32, 162, 81, 16, 2, 522, 1296, 256, 512, 2592, 261]
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

def actualOperator (rho : Representation (ZMod 2) G (Fin 12 → ZMod 2)) (t k c : G) :
    Module.End (ZMod 2) (Fin 12 → ZMod 2) :=
  let P := rho t + rho t ^ 2
  let F := 1 + P + rho c * P * rho c⁻¹
  F * rho c + rho c * P + (rho t + rho k) * P * rho c⁻¹

def algebraElement (t k c : G) : (ZMod 2)[G] :=
  let T := MonoidAlgebra.single t 1
  let K := MonoidAlgebra.single k 1
  let C := MonoidAlgebra.single c 1
  let C' := MonoidAlgebra.single c⁻¹ 1
  let P := T + T ^ 2
  let F := 1 + P + C * P * C'
  F * C + C * P + (T + K) * P * C'

theorem actualOperator_eq (rho : Representation (ZMod 2) G (Fin 12 → ZMod 2)) (t k c : G) :
    actualOperator rho t k c = rho.asAlgebraHom (algebraElement t k c) := by
  simp only [actualOperator, algebraElement, map_add, map_mul, map_pow, map_one,
    Representation.asAlgebraHom_single, one_smul]

theorem uniform_of_basis (rho : Representation (ZMod 2) G (Fin 12 → ZMod 2)) (t k c : G)
    (e : Equiv.Perm (Fin 12))
    (h : ∀ i x : Fin 12,
      actualOperator rho t k c
        (fun y ↦ (Pi.single i 1 : Fin 12 → ZMod 2) (e.symm y)) x =
          operator (Pi.single i 1) (e.symm x)) :
    UniformSubrepresentationGeneratorBound rho 1 :=
  polynomialWitness.uniform_of_reindexed_basis rho (algebraElement t k c)
    (actualOperator rho t k c) (actualOperator_eq rho t k c) e h

end SymmetricSubgroupAsymptotics.BinaryPairedTernaryCentralFlipPolynomial

end
