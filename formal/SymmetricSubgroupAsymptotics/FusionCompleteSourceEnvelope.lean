import SymmetricSubgroupAsymptotics.FusionCompleteQuotientTransfer

/-!
# Summing literal normal-axis envelopes on one complete source

Capacity and incidence arguments naturally produce one coefficient for each
literal normal axis of the original action.  This file performs only the
finite axis sum.  The complete source, surviving predicate and comparator
weight stay unchanged, so no independent-source maximum or quotient-type
identification is introduced.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

def fusionAxisEnvelopeTotal {w : ℕ}
    (U : Subgroup (Equiv.Perm (Fin w)))
    (C : {N : Subgroup U // N.Normal} → ℝ) : ℝ :=
  ∑ N, C N

theorem fusionAxisEnvelopeTotal_nonneg {w : ℕ}
    (U : Subgroup (Equiv.Perm (Fin w)))
    (C : {N : Subgroup U // N.Normal} → ℝ)
    (hC : ∀ N, 0 ≤ C N) :
    0 ≤ fusionAxisEnvelopeTotal U C := by
  unfold fusionAxisEnvelopeTotal
  exact Finset.sum_nonneg (fun i _ => hC i)

/-- Per-axis bounds with one unchanged comparator weight sum to a complete
source bound whose coefficient is the literal sum of the axis coefficients. -/
theorem fusionCompleteSourceSum_le_axisEnvelopeTotal
    {w b : ℕ}
    (U : Subgroup (Equiv.Perm (Fin w)))
    (P : Subgroup (U × Equiv.Perm (Fin b)) → Prop)
    (C : {N : Subgroup U // N.Normal} → ℝ)
    (Q : Subgroup (Equiv.Perm (Fin b)) → ℝ)
    (haxis : ∀ N J, fusionSurvivingEpiCount U P N J ≤ C N * Q J)
    (J : Subgroup (Equiv.Perm (Fin b))) :
    fusionCompleteSourceSum U P J ≤ fusionAxisEnvelopeTotal U C * Q J := by
  unfold fusionCompleteSourceSum fusionAxisEnvelopeTotal
  calc
    (∑ N : {N : Subgroup U // N.Normal},
        fusionSurvivingEpiCount U P N J) ≤ ∑ N, C N * Q J :=
      Finset.sum_le_sum (fun N _ => haxis N J)
    _ = (∑ N, C N) * Q J := by rw [Finset.sum_mul]

/-- The common exponential lift factor is charged once after summing all
literal axes.  This is the exact shape consumed by the growing comparator
transfer. -/
theorem fusionCompleteSourceSum_le_axisEnvelopeTotal_rpow
    {w b : ℕ}
    (U : Subgroup (Equiv.Perm (Fin w)))
    (P : Subgroup (U × Equiv.Perm (Fin b)) → Prop)
    (C : {N : Subgroup U // N.Normal} → ℝ)
    (Q : Subgroup (Equiv.Perm (Fin b)) → ℝ)
    (eta : ℝ)
    (haxis : ∀ N J, fusionSurvivingEpiCount U P N J ≤
      (C N * (2 : ℝ) ^ (eta * b)) * Q J)
    (J : Subgroup (Equiv.Perm (Fin b))) :
    fusionCompleteSourceSum U P J ≤
      (fusionAxisEnvelopeTotal U C * (2 : ℝ) ^ (eta * b)) * Q J := by
  let e : ℝ := (2 : ℝ) ^ (eta * b)
  calc
    fusionCompleteSourceSum U P J ≤
        fusionAxisEnvelopeTotal U (fun N => C N * e) * Q J :=
      fusionCompleteSourceSum_le_axisEnvelopeTotal U P
        (fun N => C N * e) Q (fun N K => haxis N K) J
    _ = (fusionAxisEnvelopeTotal U C * e) * Q J := by
      unfold fusionAxisEnvelopeTotal
      exact congrArg (fun x : ℝ => x * Q J)
        (Finset.sum_mul Finset.univ C e).symm

end SymmetricSubgroupAsymptotics

end
