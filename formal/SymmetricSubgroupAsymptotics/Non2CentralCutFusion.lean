import SymmetricSubgroupAsymptotics.Non2CentralCutNumerics
import SymmetricSubgroupAsymptotics.OriginalCentralCutFusion

/-!
# Installing retained section capacity in the central-prefix certificate

The module-theoretic proof supplies one retained annihilator cut together
with a bound on the trivial and nontrivial simple rows of the actual
quotient.  The numerical theorem combines those rows, and this file converts
the resulting `47/48` cost into the positive gap used by original-weight
fusion.
-/

set_option autoImplicit false
noncomputable section
open scoped MonoidAlgebra

namespace SymmetricSubgroupAsymptotics
namespace OriginalCentralCutFusion

variable {B : Type} [Group B]

/-- The exact retained cut bounds the Schur capacity of the quotient using
the maximum of its trivial row and one bound for all nontrivial rows.  The
same cut then satisfies the full section-capacity inequality. -/
theorem cost_le_of_retained_annihilator
    (A : Rep (ZMod 2) B)
    (C : {C : Submodule (ZMod 2) A // C ≤ A.ρ.invariants})
    (s t ell : Nat) (r : ℝ)
    (hs : 24 ≤ s)
    (hfixed : 16 * t ≤ 5 * s)
    (hunipotent : 8 * (t + ell) ≤ 3 * s)
    (hCdim : Module.finrank (ZMod 2) C.1 =
      non2CentralCutDimension t ell)
    (hcapacity : capacity A C ≤
      max (((t - non2CentralCutDimension t ell : Nat) : ℝ)) r)
    (hcoupled :
      2 * (t - non2CentralCutDimension t ell : Nat) + 4 * r ≤
        47 * (s : ℝ) / 48) :
    2 * (Module.finrank (ZMod 2) C.1 : ℝ) + 4 * capacity A C ≤
      47 * (s : ℝ) / 48 := by
  have hfull := non2CentralCut_full_cost_real
    s t ell r hs hfixed hunipotent hcoupled
  rw [hCdim]
  linarith

/-- A `47/48` section cost leaves the explicit central-prefix reserve
`s/768`: the physical pair action has width `2s`, the faithful top cover
uses `s` points, and fusion divides the remaining width by sixteen. -/
theorem gapParameter_ge_of_cost
    (A : Rep (ZMod 2) B)
    (C : {C : Submodule (ZMod 2) A // C ≤ A.ρ.invariants})
    (s : Nat)
    (hcost :
      2 * (Module.finrank (ZMod 2) C.1 : ℝ) + 4 * capacity A C ≤
        47 * (s : ℝ) / 48) :
    (s : ℝ) / 768 ≤ gapParameter A C (2 * s) s := by
  unfold gapParameter prefixDegree
  push_cast
  linarith

/-- Complete numerical installation from the retained annihilator data to
the positive original-weight fusion gap. -/
theorem gapParameter_ge_of_retained_annihilator
    (A : Rep (ZMod 2) B)
    (C : {C : Submodule (ZMod 2) A // C ≤ A.ρ.invariants})
    (s t ell : Nat) (r : ℝ)
    (hs : 24 ≤ s)
    (hfixed : 16 * t ≤ 5 * s)
    (hunipotent : 8 * (t + ell) ≤ 3 * s)
    (hCdim : Module.finrank (ZMod 2) C.1 =
      non2CentralCutDimension t ell)
    (hcapacity : capacity A C ≤
      max (((t - non2CentralCutDimension t ell : Nat) : ℝ)) r)
    (hcoupled :
      2 * (t - non2CentralCutDimension t ell : Nat) + 4 * r ≤
        47 * (s : ℝ) / 48) :
    (s : ℝ) / 768 ≤ gapParameter A C (2 * s) s := by
  apply gapParameter_ge_of_cost A C s
  exact cost_le_of_retained_annihilator A C s t ell r
    hs hfixed hunipotent hCdim hcapacity hcoupled

end OriginalCentralCutFusion
end SymmetricSubgroupAsymptotics

end
