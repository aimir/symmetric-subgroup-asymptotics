import SymmetricSubgroupAsymptotics.TernaryPlaneKleinPair

/-!
# Finite conjugacy certificate for ternary Klein pairs

This module contains only the finite search carrying a displayed
independent commuting involution pair in `GL₂(3)` to the standard diagonal
Klein four.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace LinearThree

set_option maxRecDepth 100000 in
theorem pair_conjugate_standardKlein_certificate :
    ∀ a b : GL3,
      a ≠ 1 → b ≠ 1 → a ≠ b →
      a ^ 2 = 1 → b ^ 2 = 1 → a * b = b * a →
      ∃ g : GL3,
        (kleinPairSubgroup a b).map (MulAut.conj g).toMonoidHom =
          DegreeSixS3Wreath.standardKleinLinearMap.range := by
  decide +kernel

end LinearThree
end SymmetricSubgroupAsymptotics

end
