/-
Copyright (c) 2026 Sébastien Palcoux and Pablo Spiga.
Released under Apache 2.0 license as described in the file LICENSE-APACHE-2.0.txt.
Ported from sharp-intermediate-subgroup-bounds, revision
522d6dfcb5d25d47455375e3df0f8a561b7b780b.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Rat.Defs

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-!
The common definitions used throughout the formalization.
-/

namespace SharpIntermediateSubgroupBounds

open scoped BigOperators

/-- The numerator of `∏_{j=1}^r (1 - p⁻ʲ)` after clearing powers of `p`. -/
def gammaNum (p r : ℕ) : ℕ :=
  ∏ j ∈ Finset.range r, (p ^ (j + 1) - 1)

/-- The common denominator of `∏_{j=1}^r (1 - p⁻ʲ)`. -/
def gammaDen (p r : ℕ) : ℕ :=
  p ^ (r * (r + 1) / 2)

/-- The finite Euler factor `γ_{p,r}`, represented exactly in `ℚ`. -/
def gammaQ (p r : ℕ) : ℚ :=
  (gammaNum p r : ℚ) / gammaDen p r

end SharpIntermediateSubgroupBounds
