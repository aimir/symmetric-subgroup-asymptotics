import SymmetricSubgroupAsymptotics.LiteralPolynomialSpanWitness
import SymmetricSubgroupAsymptotics.BinaryBitmaskCoordinates
import SymmetricSubgroupAsymptotics.PermutationSubrepresentationHead

/-! A two-generator polynomial certificate for the binary module on
three quaternary blocks. The translation has coordinates (1,-1,0), and
the rotation cycles the three blocks. For their operators t and s use
T = s + t + s*t*s². Two six-term recurrences span all twelve coordinates.

The uniform theorem applies to any representation realizing these two
operators. Its conclusion concerns every actual subrepresentation, by
the polynomial PID theorem. The finite certificates contain only the
displayed recurrences and their inverse matrix. -/

set_option autoImplicit false
noncomputable section
open scoped MonoidAlgebra BigOperators

namespace SymmetricSubgroupAsymptotics
namespace BinaryQuaternaryTriplePolynomial

def translation : Equiv.Perm (Fin 12) where
  toFun x := (#[9, 1, 5, 0, 4, 8, 3, 7, 11, 6, 10, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[3, 1, 11, 6, 4, 2, 9, 7, 5, 0, 10, 8] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def rotation : Equiv.Perm (Fin 12) where
  toFun x := (#[4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3] : Array (Fin 12))[x.val]!
  invFun x := (#[8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def representation :=
  permutationFunctionRepresentation (ZMod 2) (Equiv.Perm (Fin 12)) (Fin 12)

def operator : Module.End (ZMod 2) (Fin 12 → ZMod 2) :=
  representation rotation + representation translation +
    representation (rotation * translation * rotation ^ 2)

def vectorMask (j : Fin 2) (m : Fin 6) : ℕ :=
  ((#[#[4, 100, 1356, 2856, 687, 3436],
      #[32, 800, 2658, 2373, 1401, 2918]] : Array (Array ℕ))[j.val]!)[m.val]!

def vectors (j : Fin 2) (m : Fin 6) : Fin 12 → ZMod 2 :=
  binaryVectorOfMask 12 (vectorMask j m)

def selected (j : Fin 12) : Fin 2 × Fin 6 :=
  (finProdFinEquiv : Fin 2 × Fin 6 ≃ Fin 12).symm j

def coefficientMask (i : Fin 12) : ℕ :=
  (#[2855, 2214, 1, 236, 3938, 64, 67, 2813, 2305, 2497, 2475, 100] : Array ℕ)[i.val]!

def coefficient (i : Fin 12) : Fin 12 → ZMod 2 :=
  binaryVectorOfMask 12 (coefficientMask i)

private theorem step_checked : ∀ (j : Fin 2) (m : Fin 5) (x : Fin 12),
    vectors j m.succ x = operator (vectors j m.castSucc) x := by
  decide +kernel

private theorem point_checked : ∀ i x : Fin 12,
    (∑ j, coefficient i j * vectors (selected j).1 (selected j).2 x) =
      (Pi.single i 1 : Fin 12 → ZMod 2) x := by
  decide +kernel

def polynomialWitness : LiteralPolynomialSpanWitness operator 2 5 where
  vectors := vectors
  step j m := by
    funext x
    exact step_checked j m x
  selected := selected
  coefficient := coefficient
  point_eq := point_checked

def algebraElement {G : Type} [Group G] (t s : G) : (ZMod 2)[G] :=
  MonoidAlgebra.single s 1 + MonoidAlgebra.single t 1 +
    MonoidAlgebra.single (s * t * s ^ 2) 1

/-- A literal realization of the quaternary translation and ternary
rotation gives the same uniform bound in any acting group. -/
theorem uniform {G : Type} [Group G]
    (rho : Representation (ZMod 2) G (Fin 12 → ZMod 2)) (t s : G)
    (ht : rho t = representation translation)
    (hs : rho s = representation rotation) :
    UniformSubrepresentationGeneratorBound rho 2 := by
  apply polynomialWitness.uniform rho (algebraElement t s)
  simp only [operator, algebraElement, map_add, Representation.asAlgebraHom_single,
    one_smul, map_mul, map_pow, ht, hs]

end BinaryQuaternaryTriplePolynomial
end SymmetricSubgroupAsymptotics

end
