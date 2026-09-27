import SymmetricSubgroupAsymptotics.DiagonalFullSubmoduleEquiv
import SymmetricSubgroupAsymptotics.DiagonalInvariantSubmoduleDimensions
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Exact full-coordinate ternary weights on distinct isotypes

The factor for a coordinate set is the sum over its literal full-coordinate
subspaces. The invariant-submodule equivalence and the exact codimension
identity turn the global sum into one factor per distinct scalar label.
No basis, independent-coordinate assumption, or multiplicity correction is
introduced; all correlations inside one isotype remain in its factor.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.DiagonalFullSubmoduleWeights

open DiagonalInvariantSubmodules DiagonalFullSubmoduleEquiv

local instance submoduleFinite {I : Type*} [Fintype I] :
    Finite (Submodule (ZMod 3) (I → ZMod 3)) :=
  Finite.of_injective (fun K : Submodule (ZMod 3) (I → ZMod 3) =>
    (K : Set (I → ZMod 3))) SetLike.coe_injective

local instance fullSubmoduleFinite {I : Type*} [Fintype I] :
    Finite (FullSubmodule (k := ZMod 3) I) :=
  Finite.of_injective (fun K : FullSubmodule (k := ZMod 3) I => K.1)
    (fun _ _ h => Subtype.ext h)

local instance fullStableFinite {ι J : Type*} [Fintype ι]
    (scalar : ι → J → ZMod 3) : Finite (FullStable scalar) :=
  Finite.of_injective (fun K : FullStable scalar => K.1.1)
    (fun _ _ h => Subtype.ext (Subtype.ext h))

attribute [local instance] Fintype.ofFinite

/-- The ternary full-subspace factor of this literal coordinate set. -/
def ternaryFullWeight (I : Type*) [Fintype I] : ℕ :=
  ∑ K : FullSubmodule (k := ZMod 3) I,
    3 ^ (Fintype.card I - Module.finrank (ZMod 3) K.1)

variable {ι J : Type*} [Fintype ι] (scalar : ι → J → ZMod 3)

/-- Exact finite product of full-subspace factors on the actual
coordinate fibres of the distinct scalar functions. -/
theorem fullStable_weight_sum :
    (∑ K : FullStable scalar,
      (3 : ℕ) ^ (Fintype.card ι - Module.finrank (ZMod 3) K.1.1)) =
      ∏ a : Label scalar, ternaryFullWeight (Coordinate scalar a) := by
  calc
    _ = ∑ L : (∀ a : Label scalar,
        FullSubmodule (k := ZMod 3) (Coordinate scalar a)),
        ∏ a : Label scalar,
          (3 : ℕ) ^ (Fintype.card (Coordinate scalar a) -
            Module.finrank (ZMod 3) (L a).1) := by
      apply Fintype.sum_equiv (DiagonalFullSubmoduleEquiv.equiv scalar)
      intro K
      exact quotient_weight_factorization scalar K.1 (3 : ℕ)
    _ = _ := by
      simpa only [ternaryFullWeight, Fintype.piFinset_univ] using
        (Finset.prod_univ_sum
          (fun a : Label scalar =>
            (Finset.univ : Finset (FullSubmodule (k := ZMod 3) (Coordinate scalar a))))
          (fun a K => (3 : ℕ) ^ (Fintype.card (Coordinate scalar a) -
            Module.finrank (ZMod 3) K.1))).symm

/-- Rational weights for subsequent original-normalizer assembly use
the same exact finite sum, before any physical multiplicity divisor. -/
theorem fullStable_weight_sum_rat :
    (∑ K : FullStable scalar,
      (3 : ℚ) ^ (Fintype.card ι - Module.finrank (ZMod 3) K.1.1)) =
      ∏ a : Label scalar, (ternaryFullWeight (Coordinate scalar a) : ℚ) := by
  exact_mod_cast fullStable_weight_sum scalar

end SymmetricSubgroupAsymptotics.DiagonalFullSubmoduleWeights

end
