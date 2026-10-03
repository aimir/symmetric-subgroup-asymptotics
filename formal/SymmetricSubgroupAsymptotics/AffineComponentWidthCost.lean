import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Nat.Log

/-!
# The standard imprimitive-affine width cost

This definition is kept below the catalogue layer so the actual affine
tower and the global menu package use literally the same function.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

/-- Width-only subquadratic cost which dominates every actual choice of
local affine degree and block count. -/
noncomputable def affineComponentWidthCost (w : ℕ) : ℝ :=
  let X : ℝ := w
  let L : ℝ := (Nat.log 2 w + 1 : ℕ) ^ 2
  100 * X * Real.sqrt X * L ^ 2 +
    100 * X ^ 2 / Real.sqrt (Real.logb 2 X / 2) +
    100 * X * L

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
