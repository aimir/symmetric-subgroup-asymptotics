import SymmetricSubgroupAsymptotics.GrowingQuotientAdditiveExceptional

/-!
# Direct secondary estimates in the growing quotient transfer

The additive-tail interface originally required every cold tail to satisfy
the same subquadratic menu-mass hypothesis and every source-summed term to
have bounded width support.  Some genuine all-width owners, notably SNS2,
have to retain a fixed quadratic cost in the removed width.  Their cold row
and correlated hot scalar are still exponentially contractive together,
but neither part should be forced through those two separate interfaces.

This file isolates the secondary part of the physical recurrence and lets a
caller prove one complete forward estimate for it.  The ordinary comparator
row continues to use the reusable growing-quotient theorem unchanged.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

variable {ι : ℕ → Type*} [∀ w, Fintype (ι w)]

/-- The additive cold row and the already source-summed scalar, kept together
at the ambient degree where their joint estimate is valid. -/
def growingQuotientSecondaryError
    (w0 : ℕ) (T X : ∀ w, ι w → ℕ → ℝ)
    (A : ∀ w, ι w → ℝ) (theta : ∀ w, ι w → ℝ)
    (n : ℕ) : ℝ :=
  (∑ b ∈ Finset.range n,
      growingQuotientColdRow w0 T A theta n b * ordinarySubgroupRatio b) +
    growingQuotientExceptionalTotal w0 X n

/-- A direct estimate for the complete secondary contribution can replace
the separate tail-menu and bounded-support exceptional hypotheses.  This is
the correct integration point for a correlated all-width source moment. -/
noncomputable def
    growingQuotientAdditiveExceptional_exponentialForwardEstimate_of_secondary
    (error : ℕ → ℝ) {rho : ℝ} (w0 : ℕ)
    (D T X : ∀ w, ι w → ℕ → ℝ) (A : ∀ w, ι w → ℝ)
    (v : ∀ w, ι w → ℕ)
    (eta delta c alpha theta : ∀ w, ι w → ℝ)
    (hrho : 0 < rho) (hrho8 : rho ≤ 1 / 8) (hw0 : 3 ≤ w0)
    (hD : ∀ w i b, 0 ≤ D w i b)
    (hA : ∀ w i, 0 < A w i)
    (hparameters : GrowingQuotientParameterBound rho v eta delta c alpha)
    (hmass : GrowingMenuMassBound w0 D A)
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ)))
    (hsecondary : OrdinaryFrontierClosure.ExponentialForwardEstimate
      (growingQuotientSecondaryError w0 T X A theta))
    (hphysical : GrowingQuotientAdditiveExceptionalPhysicalBound
      error w0 D T X A v eta delta c alpha theta) :
    OrdinaryFrontierClosure.ExponentialForwardEstimate error := by
  let mainError : ℕ → ℝ := fun n =>
    growingQuotientHotTotal (fun m => (subgroupCount m : ℝ))
        w0 n D A v eta delta c +
      ∑ b ∈ Finset.range n,
        growingQuotientColdRow w0 D A alpha n b * ordinarySubgroupRatio b
  have hmainPhysical : GrowingQuotientPhysicalBound
      mainError w0 D A v eta delta c alpha :=
    Filter.Eventually.of_forall (fun _ => le_rfl)
  let Emain := growingQuotient_exponentialForwardEstimate
    mainError w0 D A v eta delta c alpha hrho hrho8 hw0
      hD hA hparameters hmass hcoarse hmainPhysical
  let E := OrdinaryFrontierClosure.ExponentialForwardEstimate.add
    Emain hsecondary
  let N : ℕ := Classical.choose (eventually_atTop.mp hphysical)
  have hN := Classical.choose_spec (eventually_atTop.mp hphysical)
  exact OrdinaryFrontierClosure.ExponentialForwardEstimate.of_le E N
    (fun n hn => by
      simpa only [mainError, growingQuotientSecondaryError, add_assoc] using
        hN n hn)

end SymmetricSubgroupAsymptotics

end
