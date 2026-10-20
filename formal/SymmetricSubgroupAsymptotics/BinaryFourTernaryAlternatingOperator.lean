import SymmetricSubgroupAsymptotics.BinaryFourTernaryCycleOperator
import SymmetricSubgroupAsymptotics.LiteralPolynomialSpanWitnessCoordinateTransport
import SymmetricSubgroupAsymptotics.BinaryBitmaskCoordinates

/-! A shared cyclic operator when the four-block action is alternating.
The constant part uses the checked A4 norm construction. On augmentation,
four actual transports give a companion operator with a local ternary
rotation and an extra last-to-second edge. A single twelve-dimensional
recurrence and inverse certificate covers all coordinate realizations. -/

set_option autoImplicit false
noncomputable section
open scoped MonoidAlgebra BigOperators

namespace SymmetricSubgroupAsymptotics
namespace BinaryFourTernaryAlternatingOperator

open BinaryFourTernaryCycleOperator

def columnMask : Fin 12 → ℕ :=
  ![4093, 4091, 1646, 1110, 4063, 4031, 1766, 1380, 3583, 3071, 3686, 1605]

def operator : Module.End (ZMod 2) (Fin 12 → ZMod 2) :=
  (binaryMatrixOfColumnMasks 12 columnMask).mulVecLin

def vectorMask : Fin 12 → ℕ :=
  ![1, 4093, 4, 1646, 259, 3577, 3477, 1780, 21, 1612, 327, 3441]

def vectors (_ : Fin 1) (m : Fin 12) : Fin 12 → ZMod 2 :=
  binaryVectorOfMask 12 (vectorMask m)

def coefficientMask : Fin 12 → ℕ :=
  ![1, 2477, 4, 4053, 261, 2981, 1044, 2037, 2492, 38, 2531, 1770]

def coefficient (i : Fin 12) : Fin 12 → ZMod 2 :=
  binaryVectorOfMask 12 (coefficientMask i)

def polynomialWitness : LiteralPolynomialSpanWitness operator 1 11 where
  vectors := vectors
  step j m := by
    funext x
    revert j m x
    decide +kernel
  selected m := (0, m)
  coefficient := coefficient
  point_eq := by decide +kernel

variable {G : Type} [Group G]

def constantActionOperator
    (rho : Representation (ZMod 2) G (Fin 12 → ZMod 2)) (a d : G) :
    Module.End (ZMod 2) (Fin 12 → ZMod 2) :=
  normOperator rho a * rho d * normOperator rho a + 1 + rho a ^ 2

def constantActionScalar (a d : G) : (ZMod 2)[G] :=
  normScalar a * MonoidAlgebra.single d 1 * normScalar a + 1 +
    MonoidAlgebra.single a 1 ^ 2

theorem constantActionOperator_eq
    (rho : Representation (ZMod 2) G (Fin 12 → ZMod 2)) (a d : G) :
    constantActionOperator rho a d = rho.asAlgebraHom (constantActionScalar a d) := by
  simp only [constantActionOperator, constantActionScalar, map_mul, map_add,
    map_pow, map_one, Representation.asAlgebraHom_single, one_smul, ← normOperator_eq]

def constantsOperator (singleBlock : Bool)
    (rho : Representation (ZMod 2) G (Fin 12 → ZMod 2)) (t a : G) (q : Fin 4 → G) :
    Module.End (ZMod 2) (Fin 12 → ZMod 2) :=
  1 + ∑ i, rho (q i) * fibreOperator singleBlock rho t a * rho (q i)⁻¹

def constantsScalar (singleBlock : Bool) (t a : G) (q : Fin 4 → G) : (ZMod 2)[G] :=
  1 + ∑ i, MonoidAlgebra.single (q i) 1 * fibreScalar singleBlock t a *
    MonoidAlgebra.single (q i)⁻¹ 1

theorem constantsOperator_eq (singleBlock : Bool)
    (rho : Representation (ZMod 2) G (Fin 12 → ZMod 2)) (t a : G) (q : Fin 4 → G) :
    constantsOperator singleBlock rho t a q =
      rho.asAlgebraHom (constantsScalar singleBlock t a q) := by
  simp only [constantsOperator, constantsScalar, map_add, map_sum, map_mul, map_one,
    Representation.asAlgebraHom_single, one_smul, ← fibreOperator_eq]

def actualOperator (singleBlock : Bool)
    (rho : Representation (ZMod 2) G (Fin 12 → ZMod 2)) (t a d : G) (q : Fin 4 → G) :
    Module.End (ZMod 2) (Fin 12 → ZMod 2) :=
  constantsOperator singleBlock rho t a q * constantActionOperator rho a d +
    (∑ i : Fin 3, rho (q i.succ) * fibreOperator singleBlock rho t a *
      rho (q i.castSucc)⁻¹) +
    rho (localRotation singleBlock t a) * fibreOperator singleBlock rho t a * rho (q 3)⁻¹ +
    rho (q 1) * fibreOperator singleBlock rho t a * rho (q 3)⁻¹

def algebraElement (singleBlock : Bool) (t a d : G) (q : Fin 4 → G) : (ZMod 2)[G] :=
  constantsScalar singleBlock t a q * constantActionScalar a d +
    (∑ i : Fin 3, MonoidAlgebra.single (q i.succ) 1 * fibreScalar singleBlock t a *
      MonoidAlgebra.single (q i.castSucc)⁻¹ 1) +
    MonoidAlgebra.single (localRotation singleBlock t a) 1 * fibreScalar singleBlock t a *
      MonoidAlgebra.single (q 3)⁻¹ 1 +
    MonoidAlgebra.single (q 1) 1 * fibreScalar singleBlock t a * MonoidAlgebra.single (q 3)⁻¹ 1

theorem actualOperator_eq (singleBlock : Bool)
    (rho : Representation (ZMod 2) G (Fin 12 → ZMod 2)) (t a d : G) (q : Fin 4 → G) :
    actualOperator singleBlock rho t a d q =
      rho.asAlgebraHom (algebraElement singleBlock t a d q) := by
  simp only [actualOperator, algebraElement, map_add, map_sum, map_mul,
    Representation.asAlgebraHom_single, one_smul, ← fibreOperator_eq,
    ← constantsOperator_eq, ← constantActionOperator_eq]

theorem uniform_of_basis (singleBlock : Bool)
    (rho : Representation (ZMod 2) G (Fin 12 → ZMod 2)) (t a d : G) (q : Fin 4 → G)
    (e : Equiv.Perm (Fin 12))
    (h : ∀ i x : Fin 12,
      actualOperator singleBlock rho t a d q
        (fun y ↦ (Pi.single i 1 : Fin 12 → ZMod 2) (e.symm y)) x =
          operator (Pi.single i 1) (e.symm x)) :
    UniformSubrepresentationGeneratorBound rho 1 :=
  polynomialWitness.uniform_of_reindexed_basis rho (algebraElement singleBlock t a d q)
    (actualOperator singleBlock rho t a d q) (actualOperator_eq singleBlock rho t a d q) e h

end BinaryFourTernaryAlternatingOperator
end SymmetricSubgroupAsymptotics

end
