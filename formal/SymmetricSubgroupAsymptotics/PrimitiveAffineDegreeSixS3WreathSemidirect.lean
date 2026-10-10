import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeSixS3WreathSemidirectMap

/-!
# Canonical ternary semidirect coordinates on `S₃ ≀ C₂`

The coordinate map is defined and proved injective in the lightweight
`PrimitiveAffineDegreeSixS3WreathSemidirectMap` module.  Equality of the
two order-72 cardinalities supplies surjectivity here, avoiding a second
full finite decision over the wreath group.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace DegreeSixS3Wreath

/-- The fixed wreath comparator is exactly its ternary monomial
semidirect model. -/
def semidirectEquiv : G ≃* SemidirectModel :=
  MulEquiv.ofBijective semidirectMap
    ((Nat.bijective_iff_injective_and_card semidirectMap).mpr
      ⟨semidirectMap_injective, card_G.trans card_SemidirectModel.symm⟩)

@[simp] theorem semidirectEquiv_right (g : G) :
    (semidirectEquiv g).right = projection g := rfl

@[simp] theorem semidirectEquiv_left (g : G) :
    (semidirectEquiv g).left =
      Multiplicative.ofAdd (ternaryCoordinates g) := rfl

end DegreeSixS3Wreath
end SymmetricSubgroupAsymptotics

end
