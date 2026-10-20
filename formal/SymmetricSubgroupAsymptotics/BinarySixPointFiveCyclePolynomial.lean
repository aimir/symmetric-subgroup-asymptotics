import SymmetricSubgroupAsymptotics.LiteralPolynomialSpanWitness
import SymmetricSubgroupAsymptotics.BinaryBitmaskCoordinates
import SymmetricSubgroupAsymptotics.PermutationSubrepresentationHead

/-! A shared cyclic polynomial operator for a five-cycle on six points.
The average E=1+a+a²+a³+a⁴ projects onto the two fixed coordinates.
If b moves the unique fixed point into the five-cycle, E*b*E exchanges
those coordinates. The complementary four-dimensional space is cyclic
under 1+a². The displayed six-dimensional certificate verifies their
combination without enumerating invariant subspaces. -/

set_option autoImplicit false
noncomputable section
open scoped MonoidAlgebra BigOperators

namespace SymmetricSubgroupAsymptotics.BinarySixPointFiveCyclePolynomial

def columnMask (j : Fin 2) (i : Fin 6) : ℕ :=
  ((#[#[37, 42, 52, 41, 50, 31], #[62, 11, 21, 41, 19, 37]] :
    Array (Array ℕ))[j.val]!)[i.val]!

def operator (j : Fin 2) : Module.End (ZMod 2) (Fin 6 → ZMod 2) :=
  (binaryMatrixOfColumnMasks 6 (columnMask j)).mulVecLin

def vectorMask (j : Fin 2) (m : Fin 6) : ℕ :=
  ((#[#[1, 37, 14, 55, 22, 44], #[2, 11, 28, 47, 44, 25]] :
    Array (Array ℕ))[j.val]!)[m.val]!

def vectors (j : Fin 2) (_ : Fin 1) (m : Fin 6) : Fin 6 → ZMod 2 :=
  binaryVectorOfMask 6 (vectorMask j m)

def coefficientMask (j : Fin 2) (i : Fin 6) : ℕ :=
  ((#[#[1, 61, 26, 35, 55, 25], #[25, 1, 61, 26, 35, 55]] :
    Array (Array ℕ))[j.val]!)[i.val]!

def coefficient (j : Fin 2) (i : Fin 6) : Fin 6 → ZMod 2 :=
  binaryVectorOfMask 6 (coefficientMask j i)

def polynomialWitness (j : Fin 2) : LiteralPolynomialSpanWitness (operator j) 1 5 where
  vectors := vectors j
  step m n := by
    funext x
    revert j m n x
    decide +kernel
  selected m := (0, m)
  coefficient := coefficient j
  point_eq := by
    revert j
    decide +kernel

def representation : Representation (ZMod 2) (Equiv.Perm (Fin 6)) (Fin 6 → ZMod 2) :=
  permutationFunctionRepresentation (ZMod 2) (Equiv.Perm (Fin 6)) (Fin 6)

variable {G : Type} [Group G]

def averagingOperator (rho : Representation (ZMod 2) G (Fin 6 → ZMod 2)) (a : G) :
    Module.End (ZMod 2) (Fin 6 → ZMod 2) :=
  1 + rho a + rho a ^ 2 + rho a ^ 3 + rho a ^ 4

def actualOperator (rho : Representation (ZMod 2) G (Fin 6 → ZMod 2)) (a b : G) :
    Module.End (ZMod 2) (Fin 6 → ZMod 2) :=
  averagingOperator rho a * rho b * averagingOperator rho a + 1 + rho a ^ 2

def averagingElement (a : G) : (ZMod 2)[G] :=
  1 + MonoidAlgebra.single a 1 + MonoidAlgebra.single a 1 ^ 2 +
    MonoidAlgebra.single a 1 ^ 3 + MonoidAlgebra.single a 1 ^ 4

def algebraElement (a b : G) : (ZMod 2)[G] :=
  averagingElement a * MonoidAlgebra.single b 1 * averagingElement a + 1 +
    MonoidAlgebra.single a 1 ^ 2

theorem actualOperator_eq
    (rho : Representation (ZMod 2) G (Fin 6 → ZMod 2)) (a b : G) :
    actualOperator rho a b = rho.asAlgebraHom (algebraElement a b) := by
  simp only [actualOperator, averagingOperator, algebraElement, averagingElement,
    map_mul, map_add, map_one, map_pow, Representation.asAlgebraHom_single, one_smul]

/-- Equalities on six coordinate basis vectors bind the polynomial
certificate to the actual group algebra, so the conclusion is uniform
over every subrepresentation of the given representation. -/
theorem uniform_of_basis (j : Fin 2)
    (rho : Representation (ZMod 2) G (Fin 6 → ZMod 2)) (a b : G)
    (h : ∀ i x : Fin 6,
      actualOperator rho a b (Pi.single i 1) x = operator j (Pi.single i 1) x) :
    UniformSubrepresentationGeneratorBound rho 1 := by
  have heq : actualOperator rho a b = operator j := by
    apply (Pi.basisFun (ZMod 2) (Fin 6)).ext
    intro i
    rw [Pi.basisFun_apply]
    exact funext (h i)
  apply (polynomialWitness j).uniform rho (algebraElement a b)
  rw [← heq]
  exact actualOperator_eq rho a b

/-- This form permits source generators to be bound once to their
actual induced pair permutations. -/
theorem uniform_of_actions (j : Fin 2)
    (rho : Representation (ZMod 2) G (Fin 6 → ZMod 2)) (a b : G)
    (p q : Equiv.Perm (Fin 6))
    (ha : rho a = representation p) (hb : rho b = representation q)
    (h : ∀ i x : Fin 6,
      actualOperator representation p q (Pi.single i 1) x =
        operator j (Pi.single i 1) x) :
    UniformSubrepresentationGeneratorBound rho 1 := by
  apply uniform_of_basis j rho a b
  simpa only [actualOperator, averagingOperator, ha, hb] using h

end SymmetricSubgroupAsymptotics.BinarySixPointFiveCyclePolynomial

end
