import SymmetricSubgroupAsymptotics.LiteralPolynomialSpanWitness
import SymmetricSubgroupAsymptotics.BinaryBitmaskCoordinates

/-! Cyclic polynomial operators built from a five-cycle average.
For operators a,b,c put E=1+a+a²+a³+a⁴ and T=c*(E*b*E+1+a²).
On a six-point block where a is a five-cycle, E projects onto the two
fixed coordinates. A suitable b interchanges these coordinates, while
1+a² acts on the four-dimensional complementary space. A block-moving
c combines the two six-point spaces.

Six displayed matrices cover the literal realizations used below,
including one with diagonal five-cycles. Each matrix has twelve spanning
iterates of delta1. The final theorem accepts equality only on the twelve
coordinate basis vectors and then applies the uniform polynomial/PID
submodule theorem. -/

set_option autoImplicit false
noncomputable section
open scoped MonoidAlgebra BigOperators

namespace SymmetricSubgroupAsymptotics
namespace BinaryFiveCycleAveragePolynomial

def columnMask (j : Fin 6) (i : Fin 12) : ℕ :=
  ((#[
    #[2048, 1092, 2, 1296, 8, 1089, 32, 1284, 128, 341, 512, 1041],
    #[512, 273, 8, 69, 2, 1281, 128, 81, 32, 1364, 2048, 1029],
    #[512, 1092, 8, 1296, 2, 1089, 128, 1284, 32, 341, 2048, 1041],
    #[2048, 69, 2, 273, 8, 1089, 32, 261, 128, 1041, 512, 1364],
    #[2048, 69, 2, 276, 8, 1092, 32, 261, 128, 1044, 512, 1361],
    #[2058, 261, 522, 1089, 648, 273, 168, 69, 2088, 1041, 2722, 1364]
    ] : Array (Array ℕ))[j.val]!)[i.val]!

def operator (j : Fin 6) : Module.End (ZMod 2) (Fin 12 → ZMod 2) :=
  (binaryMatrixOfColumnMasks 12 (columnMask j)).mulVecLin

def vectorMask (j : Fin 6) (m : Fin 12) : ℕ :=
  ((#[
    #[2, 1092, 546, 336, 168, 1109, 2602, 81, 2088, 1344, 672, 16],
    #[2, 273, 546, 324, 168, 1301, 2602, 1284, 2088, 321, 672, 4],
    #[2, 1092, 2184, 1029, 2568, 84, 138, 1104, 2178, 1361, 2722, 69],
    #[2, 69, 2082, 336, 168, 1109, 2602, 1104, 552, 321, 2208, 16],
    #[2, 69, 2082, 336, 168, 1109, 2602, 1104, 552, 324, 162, 1284],
    #[2, 261, 552, 321, 138, 1281, 2688, 256, 2088, 4, 522, 341]
    ] : Array (Array ℕ))[j.val]!)[m.val]!

def vectors (j : Fin 6) (_ : Fin 1) (m : Fin 12) : Fin 12 → ZMod 2 :=
  binaryVectorOfMask 12 (vectorMask j m)

def coefficientMask (j : Fin 6) (i : Fin 12) : ℕ :=
  ((#[
    #[2082, 1, 2728, 1361, 2048, 324, 162, 1029, 2218, 321, 2568, 1301],
    #[2568, 1, 2048, 1361, 2728, 324, 2218, 1029, 162, 321, 2082, 1301],
    #[168, 1, 2058, 261, 2184, 1104, 162, 324, 552, 336, 2218, 69],
    #[2568, 1, 2728, 1361, 2048, 324, 162, 1029, 2218, 1301, 2082, 321],
    #[2088, 1, 2184, 1041, 2688, 324, 162, 1349, 2602, 1109, 2722, 321],
    #[642, 1, 512, 341, 2568, 1029, 522, 324, 128, 1364, 546, 1104]
    ] : Array (Array ℕ))[j.val]!)[i.val]!

def coefficient (j : Fin 6) (i : Fin 12) : Fin 12 → ZMod 2 :=
  binaryVectorOfMask 12 (coefficientMask j i)

private theorem step_checked : ∀ (j : Fin 6) (m : Fin 11) (x : Fin 12),
    vectors j 0 m.succ x = operator j (vectors j 0 m.castSucc) x := by
  decide +kernel

private theorem point_checked : ∀ (j : Fin 6) (i x : Fin 12),
    (∑ m, coefficient j i m * vectors j 0 m x) =
      (Pi.single i 1 : Fin 12 → ZMod 2) x := by
  decide +kernel

def polynomialWitness (j : Fin 6) : LiteralPolynomialSpanWitness (operator j) 1 11 where
  vectors := vectors j
  step _ m := by
    funext x
    exact step_checked j m x
  selected m := (0, m)
  coefficient := coefficient j
  point_eq := point_checked j

def averagingOperator {G : Type} [Group G]
    (rho : Representation (ZMod 2) G (Fin 12 → ZMod 2)) (a : G) :
    Module.End (ZMod 2) (Fin 12 → ZMod 2) :=
  1 + rho a + rho (a ^ 2) + rho (a ^ 3) + rho (a ^ 4)

def actualOperator {G : Type} [Group G]
    (rho : Representation (ZMod 2) G (Fin 12 → ZMod 2)) (a b c : G) :
    Module.End (ZMod 2) (Fin 12 → ZMod 2) :=
  rho c * (averagingOperator rho a * rho b * averagingOperator rho a + 1 + rho (a ^ 2))

def averagingElement {G : Type} [Group G] (a : G) : (ZMod 2)[G] :=
  1 + MonoidAlgebra.single a 1 + MonoidAlgebra.single (a ^ 2) 1 +
    MonoidAlgebra.single (a ^ 3) 1 + MonoidAlgebra.single (a ^ 4) 1

def algebraElement {G : Type} [Group G] (a b c : G) : (ZMod 2)[G] :=
  MonoidAlgebra.single c 1 *
    (averagingElement a * MonoidAlgebra.single b 1 * averagingElement a + 1 +
      MonoidAlgebra.single (a ^ 2) 1)

theorem actualOperator_eq {G : Type} [Group G]
    (rho : Representation (ZMod 2) G (Fin 12 → ZMod 2)) (a b c : G) :
    actualOperator rho a b c = rho.asAlgebraHom (algebraElement a b c) := by
  simp only [actualOperator, averagingOperator, algebraElement, averagingElement,
    map_mul, map_add, map_one, Representation.asAlgebraHom_single, one_smul]

/-- A basis-vector check binds a displayed cyclic polynomial operator to
an arbitrary acting group, giving the bound for every subrepresentation. -/
theorem uniform_of_basis {G : Type} [Group G] (j : Fin 6)
    (rho : Representation (ZMod 2) G (Fin 12 → ZMod 2)) (a b c : G)
    (h : ∀ i x : Fin 12,
      actualOperator rho a b c (Pi.single i 1) x = operator j (Pi.single i 1) x) :
    UniformSubrepresentationGeneratorBound rho 1 := by
  have heq : actualOperator rho a b c = operator j := by
    apply (Pi.basisFun (ZMod 2) (Fin 12)).ext
    intro i
    rw [Pi.basisFun_apply]
    exact funext (h i)
  apply (polynomialWitness j).uniform rho (algebraElement a b c)
  rw [← heq]
  exact actualOperator_eq rho a b c

end BinaryFiveCycleAveragePolynomial
end SymmetricSubgroupAsymptotics

end
