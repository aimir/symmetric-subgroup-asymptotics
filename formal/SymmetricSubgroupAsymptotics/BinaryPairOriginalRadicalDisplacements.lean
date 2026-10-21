import SymmetricSubgroupAsymptotics.BinaryPairOriginalCoordinateRepresentation
import SymmetricSubgroupAsymptotics.RepresentationIntrinsicRadicalDisplacement
import Mathlib.Algebra.Field.ZMod

/-! The same original coordinate action kills its invariant state modulo
the whole original intrinsic radical. No element enumeration is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

variable {X : Type} {w : ℕ} {U : Subgroup (Equiv.Perm X)}
    (E : BinaryPairFrame U (Fin w))

theorem originalCoordinate_displacement_mem_of_intrinsic_radical
    (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) U X))
    (S R : Submodule (ZMod 2) (Fin (w+w) → ZMod 2))
    (hS : (E.originalCoordinateSubrepresentation W).toSubmodule = S)
    (hR : ((Representation.Coinvariants.ker W.toRepresentation).map
      W.toSubmodule.subtype).map E.originalCoordinateEquiv.toLinearMap = R)
    (g : U) (v : Fin (w+w) → ZMod 2) (hv : v ∈ S) :
    E.originalCoordinateRepresentation g v - v ∈ R := by
  have hr : (Representation.Coinvariants.ker
      (E.originalCoordinateSubrepresentation W).toRepresentation).map
        (E.originalCoordinateSubrepresentation W).toSubmodule.subtype = R :=
    (RepresentationCoordinateChange.subrepresentation_radical
      (permutationFunctionRepresentation (ZMod 2) U X) E.originalCoordinateEquiv W).symm.trans hR
  exact subrepresentation_displacement_mem_of_radical_eq E.originalCoordinateRepresentation
    (E.originalCoordinateSubrepresentation W) S R hS hr g v hv

end SymmetricSubgroupAsymptotics.BinaryPairFrame
