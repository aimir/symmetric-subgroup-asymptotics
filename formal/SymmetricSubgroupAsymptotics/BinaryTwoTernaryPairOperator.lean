import SymmetricSubgroupAsymptotics.RepresentationAlgebraCyclicPointBasis
import SymmetricSubgroupAsymptotics.PermutationSubrepresentationHead

/-! A uniform cyclic six-point module for a local ternary rotation and
three literal movers of its two blocks. The algebra operator replaces
the return map on augmentation while retaining the swap on constants.
This permits a mover with reflection monodromy as well as an involution. -/

set_option autoImplicit false
noncomputable section
open scoped MonoidAlgebra

namespace SymmetricSubgroupAsymptotics.BinaryTwoTernaryPairOperator

def rotation : Equiv.Perm (Fin 6) where
  toFun := ![2, 1, 4, 3, 0, 5]
  invFun := ![4, 1, 0, 3, 2, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def mover (j : Fin 3) : Equiv.Perm (Fin 6) where
  toFun x := ((#[#[3, 4, 1, 0, 5, 2], #[3, 4, 5, 0, 1, 2], #[1, 0, 5, 4, 3, 2]] :
    Array (Array (Fin 6)))[j.val]!)[x.val]!
  invFun x := ((#[#[3, 2, 5, 0, 1, 4], #[3, 4, 5, 0, 1, 2], #[1, 0, 5, 4, 3, 2]] :
    Array (Array (Fin 6)))[j.val]!)[x.val]!
  left_inv := by revert j; decide +kernel
  right_inv := by revert j; decide +kernel

def pointCycle (j : Fin 3) : Equiv.Perm (Fin 6) where
  toFun x := ((#[#[0, 3, 2, 1, 4, 5], #[0, 3, 2, 5, 4, 1], #[0, 1, 2, 5, 4, 3]] :
    Array (Array (Fin 6)))[j.val]!)[x.val]!
  invFun x := ((#[#[0, 3, 2, 1, 4, 5], #[0, 5, 2, 1, 4, 3], #[0, 1, 2, 5, 4, 3]] :
    Array (Array (Fin 6)))[j.val]!)[x.val]!
  left_inv := by revert j; decide +kernel
  right_inv := by revert j; decide +kernel

def representation : Representation (ZMod 2) (Equiv.Perm (Fin 6)) (Fin 6 → ZMod 2) :=
  permutationFunctionRepresentation (ZMod 2) (Equiv.Perm (Fin 6)) (Fin 6)

variable {G : Type} [Group G]

def fibreOperator (rho : Representation (ZMod 2) G (Fin 6 → ZMod 2)) (t : G) :
    Module.End (ZMod 2) (Fin 6 → ZMod 2) := rho t + rho t ^ 2

def fibreScalar (t : G) : (ZMod 2)[G] :=
  MonoidAlgebra.single t 1 + MonoidAlgebra.single t 1 ^ 2

def actualOperator (rho : Representation (ZMod 2) G (Fin 6 → ZMod 2)) (t c : G) :
    Module.End (ZMod 2) (Fin 6 → ZMod 2) :=
  (1 + fibreOperator rho t + rho c * fibreOperator rho t * rho c⁻¹) * rho c +
    rho c * fibreOperator rho t + rho t * fibreOperator rho t * rho c⁻¹

def algebraElement (t c : G) : (ZMod 2)[G] :=
  (1 + fibreScalar t + MonoidAlgebra.single c 1 * fibreScalar t *
    MonoidAlgebra.single c⁻¹ 1) * MonoidAlgebra.single c 1 +
    MonoidAlgebra.single c 1 * fibreScalar t +
    MonoidAlgebra.single t 1 * fibreScalar t * MonoidAlgebra.single c⁻¹ 1

theorem actualOperator_eq
    (rho : Representation (ZMod 2) G (Fin 6 → ZMod 2)) (t c : G) :
    actualOperator rho t c = rho.asAlgebraHom (algebraElement t c) := by
  simp only [actualOperator, algebraElement, fibreOperator, fibreScalar,
    map_add, map_mul, map_one, map_pow, Representation.asAlgebraHom_single, one_smul]

def operator (j : Fin 3) : Module.End (ZMod 2) (Fin 6 → ZMod 2) :=
  actualOperator representation rotation (mover j)

def polynomialWitness (j : Fin 3) : LiteralPolynomialSpanWitness (operator j) 1 5 :=
  algebraPointCycleWitness (operator j) (pointCycle j) (by
    intro m
    funext x
    revert j m x
    decide +kernel)

theorem uniform (j : Fin 3)
    (rho : Representation (ZMod 2) G (Fin 6 → ZMod 2)) (t c : G)
    (ht : rho t = representation rotation)
    (hc : rho c = representation (mover j))
    (hci : rho c⁻¹ = representation (mover j)⁻¹) :
    UniformSubrepresentationGeneratorBound rho 1 := by
  apply (polynomialWitness j).uniform rho (algebraElement t c)
  rw [← actualOperator_eq]
  simp only [operator, actualOperator, fibreOperator, ht, hc, hci]

theorem uniform_subgroup (j : Fin 3) (H : Subgroup (Equiv.Perm (Fin 6)))
    (t c : H)
    (ht : (t : Equiv.Perm (Fin 6)) = rotation)
    (hc : (c : Equiv.Perm (Fin 6)) = mover j) :
    UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) H (Fin 6)) 1 := by
  have action_eq (g : H) (p : Equiv.Perm (Fin 6))
      (h : (g : Equiv.Perm (Fin 6)) = p) :
      permutationFunctionRepresentation (ZMod 2) H (Fin 6) g = representation p := by
    apply LinearMap.ext
    intro v
    funext x
    change v ((g : Equiv.Perm (Fin 6))⁻¹ x) = v (p⁻¹ x)
    rw [h]
  apply uniform j _ t c (action_eq t _ ht) (action_eq c _ hc)
  apply action_eq
  change (c : Equiv.Perm (Fin 6))⁻¹ = (mover j)⁻¹
  rw [hc]

end SymmetricSubgroupAsymptotics.BinaryTwoTernaryPairOperator

end
