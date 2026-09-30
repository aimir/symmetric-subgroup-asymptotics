import SymmetricSubgroupAsymptotics.Non2PreE7ExceptionalCatalogueAssembly
import SymmetricSubgroupAsymptotics.Non2PreE7JointTopYonedaIncidence

/-!
# Restrict terminal joint top/Yoneda cells to the mixed owner catalogue

Adding source-summed B6 certificates enlarges the earlier-owner predicate.
Consequently its terminal branch is a restriction of the previously proved
terminal branch.  This file proves that monotonicity on the complete physical
subgroup and reuses every retained joint top/Yoneda cell unchanged.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

/-- Every pointwise comparator action is also an action of the mixed local
catalogue. -/
theorem preE7NoPairNoC3EarlierFamilyPredicate_comparator_le_local
    (n : ℕ) (k : Fin preE7NoPairNoC3EarlierOwnerCount)
    (H : Subgroup (Equiv.Perm (Fin n))) :
    preE7NoPairNoC3EarlierFamilyPredicate
        preE7NoPairNoC3EarlierFamilyAction n k H →
      preE7NoPairNoC3EarlierFamilyPredicate
        preE7NoPairNoC3EarlierLocalFamilyAction n k H := by
  rintro ⟨W⟩
  refine ⟨{ W with applies := ?_ }⟩
  exact preE7EarlierLocalFamilyAction_ofComparator
    (Classical.choice W.applies)

/-- First ownership by the enlarged catalogue's terminal branch implies
first ownership by the old comparator-only terminal branch. -/
theorem preE7NoPairNoC3Local_terminal_implies_comparator_terminal
    (w b : ℕ) (U : PreE7NonPairActionClass w)
    (H : Subgroup (preE7NonPairAction w U × Equiv.Perm (Fin b))) :
    preE7NoPairNoC3CertifiedFirstOwnerPredicate
        preE7NoPairNoC3EarlierLocalFamilyAction w
        (Fin.last preE7NoPairNoC3EarlierOwnerCount, U) b H →
      preE7NoPairNoC3CertifiedFirstOwnerPredicate
        preE7NoPairNoC3EarlierFamilyAction w
        (Fin.last preE7NoPairNoC3EarlierOwnerCount, U) b H := by
  rintro ⟨⟨howner, hnoC3⟩, _hselected⟩
  rcases howner with ⟨hordinary, hfirst⟩
  let K : Subgroup (Equiv.Perm (Fin (w + b))) :=
    relabelSubgroup finSumFinEquiv
      (H.map (fusionOrbitAction (preE7NonPairAction w U)))
  have hunownedLocal : ∀ k : Fin preE7NoPairNoC3EarlierOwnerCount,
      ¬ preE7NoPairNoC3EarlierFamilyPredicate
        preE7NoPairNoC3EarlierLocalFamilyAction (w + b) k K :=
    (firstOwned_ownerOrResidual_last_iff
      (preE7NoPairNoC3EarlierFamilyPredicate
        preE7NoPairNoC3EarlierLocalFamilyAction) K).mp hfirst
  have hunownedComparator : ∀ k : Fin preE7NoPairNoC3EarlierOwnerCount,
      ¬ preE7NoPairNoC3EarlierFamilyPredicate
        preE7NoPairNoC3EarlierFamilyAction (w + b) k K := by
    intro k hk
    exact hunownedLocal k
      (preE7NoPairNoC3EarlierFamilyPredicate_comparator_le_local
        (w + b) k K hk)
  have hfirstComparator : FirstOwned
      (ownerOrResidualEligible
        (preE7NoPairNoC3EarlierFamilyPredicate
          preE7NoPairNoC3EarlierFamilyAction) (w + b))
      (Fin.last preE7NoPairNoC3EarlierOwnerCount) K :=
    (firstOwned_ownerOrResidual_last_iff
      (preE7NoPairNoC3EarlierFamilyPredicate
        preE7NoPairNoC3EarlierFamilyAction) K).mpr hunownedComparator
  refine ⟨⟨⟨hordinary, ?_⟩, hnoC3⟩,
    preE7NoPairNoC3SelectedActionEligible_last _ U⟩
  simpa only [K] using hfirstComparator

/-- Existing joint top/Yoneda terminal data gives the terminal local row for
the enlarged ordinary/source-summed catalogue by restriction. -/
noncomputable def
    PreE7NoPairNoC3LocalExceptionalChoice.ofResidualJointTopCells
    {w : ℕ} {U : PreE7NonPairActionClass w}
    (D : PreE7ResidualJointTopCellSourceData w U) :
    PreE7NoPairNoC3LocalExceptionalChoice w
      (Fin.last preE7NoPairNoC3EarlierOwnerCount, U) := by
  let Q := PreE7NoPairNoC3AxisComparatorChoice.ofResidualJointTopCells D
  exact
    { D := fun b => fusionAxisEnvelopeTotal (preE7NonPairAction w U) (Q.C b)
      T := fun b => fusionAxisEnvelopeTotal
        (preE7NonPairAction w U) (Q.tailCoefficient b)
      X := fun _ => 0
      v := Q.v
      eta := Q.eta
      delta := Q.delta
      cutoff := Q.cutoff
      alpha := Q.alpha
      theta := Q.theta
      alpha_eq := Q.alpha_eq
      D_nonneg := fun b =>
        fusionAxisEnvelopeTotal_nonneg _ _ (Q.coefficient_nonneg b)
      T_nonneg := fun b =>
        fusionAxisEnvelopeTotal_nonneg _ _ (Q.tail_nonneg b)
      exceptional := fun _ =>
        { threshold := 0
          rate := 1
          constant := 1
          rate_pos := by norm_num
          constant_pos := by norm_num
          bound := by simp }
      exceptional_support := Or.inl rfl
      local_bound := by
        intro b
        let Pnew := preE7NoPairNoC3CertifiedFirstOwnerPredicate
          preE7NoPairNoC3EarlierLocalFamilyAction w
          (Fin.last preE7NoPairNoC3EarlierOwnerCount, U) b
        let Dmain : ℝ := fusionAxisEnvelopeTotal
          (preE7NonPairAction w U) (Q.C b)
        let Ttail : ℝ := fusionAxisEnvelopeTotal
          (preE7NonPairAction w U) (Q.tailCoefficient b)
        have hsource (J : Subgroup (Equiv.Perm (Fin b))) :
            fusionCompleteSourceSum (preE7NonPairAction w U) Pnew J ≤
              (Dmain * (2 : ℝ) ^ (Q.eta * b)) *
                  completeQuotientWeight (R := Q.R) J +
                Ttail * (2 : ℝ) ^ (Q.theta * b) := by
          unfold fusionCompleteSourceSum Dmain Ttail fusionAxisEnvelopeTotal
          calc
            _ ≤ ∑ N,
                ((Q.C b N * (2 : ℝ) ^ (Q.eta * b)) *
                    completeQuotientWeight (R := Q.R) J +
                  Q.tailCoefficient b N *
                    (2 : ℝ) ^ (Q.theta * b)) :=
              Finset.sum_le_sum (fun N _ =>
                (fusionSurvivingEpiCount_mono
                  (preE7NoPairNoC3Local_terminal_implies_comparator_terminal
                    w b U) N J).trans (Q.axis_envelope b N J))
            _ = _ := by
              simp only [Finset.sum_add_distrib, Finset.sum_mul]
              apply congrArg₂ (· + ·)
              · apply Finset.sum_congr rfl
                intro x hx
                ring
              · apply Finset.sum_congr rfl
                intro x hx
                ring
        have h := fusionPhysical_growingQuotient_additiveTail_kernel_bound
          (preE7NonPairAction w U) Pnew
          (preE7NoPairNoC3CertifiedFirstOwnerPredicate_natural _ w
            (Fin.last preE7NoPairNoC3EarlierOwnerCount, U) b)
          Q.action Q.action_injective Dmain Ttail Q.eta Q.theta Q.delta
          Q.cutoff
          (fusionAxisEnvelopeTotal_nonneg _ _ (Q.coefficient_nonneg b))
          (fusionAxisEnvelopeTotal_nonneg _ _ (Q.tail_nonneg b)) hsource
        simpa only [Pnew, Dmain, Ttail, Q.alpha_eq, add_zero] using h }

/-- Joint top/Yoneda data for every terminal action now assembles directly
with the mixed earlier-owner catalogue. -/
noncomputable def
    preE7NoPairNoC3_localExceptionalData_of_residualJointTopCells
    (D : ∀ w (U : PreE7NonPairActionClass w),
      PreE7ResidualJointTopCellSourceData w U) :
    PreE7NoPairNoC3LocalExceptionalData
      preE7NoPairNoC3EarlierOwnerCount :=
  preE7NoPairNoC3_localExceptionalData_of_residual
    (fun _ _ =>
      PreE7NoPairNoC3LocalExceptionalChoice.ofResidualJointTopCells (D _ _))

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
