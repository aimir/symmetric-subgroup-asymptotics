import SymmetricSubgroupAsymptotics.C1A4QuotientTopEpi

/-!
# Canonical physical bound for the degree-twelve prime-base owner

The internal A4 quotient theorem already removes every numerical top-map
premise from the original-normal physical estimate.  This file installs that
result on the canonical width-twelve family used by the finite continuation.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
open TernaryA4InvariantSubmodules
namespace C1TernaryPrimeBaseOwnerWitness

/-- The complete canonical width-twelve cell has the unconditional
prime-base row, with every literal normal axis and the original normalizer
retained. -/
theorem widthCanonical_bound_internal_top
    (U : Subgroup (Equiv.Perm (Fin 12)))
    (W : C1TernaryPrimeBaseOwnerWitness U)
    (b : ℕ)
    (P : Subgroup (U × Equiv.Perm (Fin b)) → Prop)
    (hP : FusionOrbitNatural U P) :
    (Nat.card (FusionWidthCanonicalFamily U (by omega : 12 ≤ b + 12) P) : ℝ) /
        exactBenchmark (b + 12) ≤
      c1EarlierKernel b .degreeTwelve
        (∑ N : {N : Subgroup U // N.Normal},
          (originalNormalRegularConstant 3 W.top W.baseModule W.baseChart N : ℝ) *
            max 1 (Nat.card (A4 ≃* A4) : ℝ))
        (Nat.card (Subgroup.normalizer (U : Set (Equiv.Perm (Fin 12)))) : ℝ) *
        ordinarySubgroupRatio b := by
  rw [fusionWidthCanonicalFamily_card]
  simpa only [ordinarySubgroupRatio] using
    W.physical_owner_bound_internal_top U b P hP

end C1TernaryPrimeBaseOwnerWitness
end SymmetricSubgroupAsymptotics

end
