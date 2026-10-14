import SymmetricSubgroupAsymptotics.LiteralPolynomialSpanWitness
import SymmetricSubgroupAsymptotics.BinaryBitmaskCoordinates
import SymmetricSubgroupAsymptotics.RepresentationGeneratorRestrictionMaschke
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows51To100

/-!
# A cyclic polynomial operator for the literal row72 natural module

Let g and s be the displayed first and second generators, and b=sgs⁻¹.
Use the group-algebra operator s+(1+g+g²)b. The norm of g isolates its
fixed triple on the ternary augmentation part, while its action on block
constants is the identity. The twelve displayed iterates of one vector
and the inverse coefficients below certify cyclicity directly.

Every finite check is a twelve-coordinate recurrence or inverse equation.
No group enumeration, invariant-subspace list, or rank assertion is used
as a proof premise. The literal top and its natural action are unchanged.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical MonoidAlgebra BigOperators

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoTwelveRow72AlgebraPolynomial

open DegreeTwoTwelvePairFiniteCatalogue

def g : Row72Top :=
  ⟨row72Generators 0, Subgroup.subset_closure (Set.mem_range_self 0)⟩

def s : Row72Top :=
  ⟨row72Generators 1, Subgroup.subset_closure (Set.mem_range_self 1)⟩

def b : Row72Top := s * g * s⁻¹

def representation := permutationFunctionRepresentation (ZMod 2) Row72Top (Fin 12)

def operator : Module.End (ZMod 2) (Fin 12 → ZMod 2) :=
  representation s + representation b + representation (g * b) +
    representation (g ^ 2 * b)

def algebraElement : (ZMod 2)[Row72Top] :=
  MonoidAlgebra.single s 1 + MonoidAlgebra.single b 1 +
    MonoidAlgebra.single (g * b) 1 + MonoidAlgebra.single (g ^ 2 * b) 1

theorem operator_eq : operator = representation.asAlgebraHom algebraElement := by
  simp only [operator, algebraElement, map_add,
    Representation.asAlgebraHom_single, one_smul]

def vectorMask (m : Fin 12) : ℕ :=
  (#[1, 24, 2376, 3585, 3825, 1695, 1515, 3915, 2638, 629, 697, 1241] : Array ℕ)[m.val]!

def vectors (_j : Fin 1) (m : Fin 12) : Fin 12 → ZMod 2 :=
  binaryVectorOfMask 12 (vectorMask m)

def coefficientMask (i : Fin 12) : ℕ :=
  (#[1, 1103, 1429, 3555, 3553, 911, 2885, 1331, 609, 703, 1653, 1219] : Array ℕ)[i.val]!

def coefficient (i : Fin 12) : Fin 12 → ZMod 2 :=
  binaryVectorOfMask 12 (coefficientMask i)

private theorem step_checked : ∀ (j : Fin 1) (m : Fin 11) (x : Fin 12),
    vectors j m.succ x = operator (vectors j m.castSucc) x := by
  decide +kernel

private theorem point_checked : ∀ i x : Fin 12,
    (∑ j, coefficient i j * vectors 0 j x) = (Pi.single i 1 : Fin 12 → ZMod 2) x := by
  decide +kernel

def polynomialWitness : LiteralPolynomialSpanWitness operator 1 11 where
  vectors := vectors
  step j m := by
    funext x
    exact step_checked j m x
  selected j := (0, j)
  coefficient := coefficient
  point_eq := point_checked

theorem natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row72Interface.top (Fin 12)) 1 :=
  polynomialWitness.uniform representation algebraElement operator_eq

/-- The same literal natural-module theorem applies to every containing
top acting on these same twelve points. -/
theorem natural_of_le {T : Subgroup (Equiv.Perm (Fin 12))}
    (h : Row72Top ≤ T) : UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) T (Fin 12)) 1 := by
  apply UniformSubrepresentationGeneratorBound.of_comp
    (permutationFunctionRepresentation (ZMod 2) T (Fin 12)) (Subgroup.inclusion h)
  change UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) Row72Top (Fin 12)) 1
  exact natural

end DegreeTwoTwelveRow72AlgebraPolynomial
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
