import SymmetricSubgroupAsymptotics.LiteralPolynomialSpanWitness
import SymmetricSubgroupAsymptotics.BinaryBitmaskCoordinates

/-! Three uniform generators for the regular alternating-four module.
For a ternary element t and two independent normal Klein-four elements
u,v, put S=1+u+v+uv and T=t+S in the binary acting algebra. The norm S
is central and square-zero; hence T²=t² and T⁴=t. The three Klein fibre
vectors 1,u,v generate over the algebra containing t and S.

The displayed recurrence and inverse certificate realizes this argument
on twelve coordinates. The generic conclusion follows from the checked
polynomial/PID submodule theorem, not just ambient generation. -/

set_option autoImplicit false
noncomputable section
open scoped MonoidAlgebra BigOperators

namespace SymmetricSubgroupAsymptotics.BinaryKleinNormTriplePolynomial

def columnMask (i : Fin 12) : ℕ :=
  (#[841, 1178, 2342, 589, 1171, 2468, 617, 1234, 2356, 2633, 1682, 3364] :
    Array ℕ)[i.val]!

def operator : Module.End (ZMod 2) (Fin 12 → ZMod 2) :=
  (binaryMatrixOfColumnMasks 12 columnMask).mulVecLin

def vectorMask (j : Fin 3) (m : Fin 6) : ℕ :=
  ((#[#[1, 841, 16, 1171, 256, 2356],
      #[8, 589, 2, 1178, 4, 2342],
      #[64, 617, 128, 1234, 32, 2468]] : Array (Array ℕ))[j.val]!)[m.val]!

def vectors (j : Fin 3) (m : Fin 6) : Fin 12 → ZMod 2 :=
  binaryVectorOfMask 12 (vectorMask j m)

def selected : Fin 12 → Fin 3 × Fin 6 :=
  ![(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5),
    (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]

def coefficientMask (i : Fin 12) : ℕ :=
  (#[1, 256, 146, 64, 4, 1042, 512, 2048, 16, 595, 2317, 1204] : Array ℕ)[i.val]!

def coefficient (i : Fin 12) : Fin 12 → ZMod 2 :=
  binaryVectorOfMask 12 (coefficientMask i)

private theorem step_checked : ∀ (j : Fin 3) (m : Fin 5) (x : Fin 12),
    vectors j m.succ x = operator (vectors j m.castSucc) x := by
  decide +kernel

private theorem point_checked : ∀ i x : Fin 12,
    (∑ j, coefficient i j * vectors (selected j).1 (selected j).2 x) =
      (Pi.single i 1 : Fin 12 → ZMod 2) x := by
  decide +kernel

def polynomialWitness : LiteralPolynomialSpanWitness operator 3 5 where
  vectors := vectors
  step j m := by
    funext x
    exact step_checked j m x
  selected := selected
  coefficient := coefficient
  point_eq := point_checked

variable {G : Type} [Group G]

def actualOperator (rho : Representation (ZMod 2) G (Fin 12 → ZMod 2)) (t u v : G) :
    Module.End (ZMod 2) (Fin 12 → ZMod 2) :=
  rho t + (1 + rho u + rho v + rho u * rho v)

def algebraElement (t u v : G) : (ZMod 2)[G] :=
  MonoidAlgebra.single t 1 + (1 + MonoidAlgebra.single u 1 +
    MonoidAlgebra.single v 1 + MonoidAlgebra.single u 1 * MonoidAlgebra.single v 1)

theorem actualOperator_eq
    (rho : Representation (ZMod 2) G (Fin 12 → ZMod 2)) (t u v : G) :
    actualOperator rho t u v = rho.asAlgebraHom (algebraElement t u v) := by
  simp only [actualOperator, algebraElement, map_mul, map_add, map_one,
    Representation.asAlgebraHom_single, one_smul]

/-- The regular Klein-norm template bounds every subrepresentation by
three generators whenever its actual algebra action is realized. -/
theorem uniform_of_basis
    (rho : Representation (ZMod 2) G (Fin 12 → ZMod 2)) (t u v : G)
    (h : ∀ i x : Fin 12,
      actualOperator rho t u v (Pi.single i 1) x = operator (Pi.single i 1) x) :
    UniformSubrepresentationGeneratorBound rho 3 := by
  have heq : actualOperator rho t u v = operator := by
    apply (Pi.basisFun (ZMod 2) (Fin 12)).ext
    intro i
    rw [Pi.basisFun_apply]
    exact funext (h i)
  apply polynomialWitness.uniform rho (algebraElement t u v)
  rw [← heq]
  exact actualOperator_eq rho t u v

end SymmetricSubgroupAsymptotics.BinaryKleinNormTriplePolynomial

end
