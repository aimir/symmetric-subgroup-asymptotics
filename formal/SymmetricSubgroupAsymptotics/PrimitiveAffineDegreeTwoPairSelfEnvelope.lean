import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairSummedSource

/-!
# The zero-kernel pair quotient

When the signed pair quotient acts faithfully on its block top there is no
binary pair kernel to estimate.  Its complete quotient sum is retained as
the comparator moment itself.  This tiny raw package is kept separate from
the central-product source so the degree-three prepend can use it without a
classification dependency.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

/-- Identity complete-moment envelope on an arbitrary literal finite
group.  The caller separately supplies whatever faithful small action it
has retained for `Q`. -/
noncomputable def preE7DegreeTwoPairQuotientSelfEnvelope
    (Q : Type) [Group Q] [Finite Q] :
    PreE7DegreeTwoPairQuotientSummedEnvelope Q where
  R := Q
  mainCoefficient := 1
  coldCoefficient := fun _ => 0
  eta := 0
  theta := 0
  mainCoefficient_nonneg := zero_le_one
  coldCoefficient_nonneg := fun _ => le_rfl
  exceptionalRaw := fun _ => 0
  exceptionalRaw_nonneg := fun _ => le_rfl
  summed := fun b => by
    simp

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
