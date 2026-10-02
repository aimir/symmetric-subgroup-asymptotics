import SymmetricSubgroupAsymptotics.BinaryAbelianization
import Mathlib.Data.Real.Basic

/-! # The binary-rank hot predicate -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

/-- The hot set of the binary rank at threshold `a`: `d₂(J) > a b`. -/
def BinaryRankHot (a : ℝ) {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))) : Prop :=
  a * b < binaryCharacterRank J

end SymmetricSubgroupAsymptotics

end
