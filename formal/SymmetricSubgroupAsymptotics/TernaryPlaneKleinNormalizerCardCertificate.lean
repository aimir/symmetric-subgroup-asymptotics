import SymmetricSubgroupAsymptotics.TernaryPlaneKleinPair

/-!
# Finite cardinal certificate for ternary Klein normalizers

This module contains only the finite calculation showing that the
normalizer of a displayed independent commuting involution pair in
`GL₂(3)` has order eight.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace LinearThree

set_option maxRecDepth 100000 in
theorem pair_normalizer_card_eq_eight_certificate :
    ∀ a b : GL3,
      a ≠ 1 → b ≠ 1 → a ≠ b →
      a ^ 2 = 1 → b ^ 2 = 1 → a * b = b * a →
      Nat.card (Subgroup.normalizer (kleinPairSubgroup a b : Set GL3)) = 8 := by
  decide +kernel

end LinearThree
end SymmetricSubgroupAsymptotics

end
