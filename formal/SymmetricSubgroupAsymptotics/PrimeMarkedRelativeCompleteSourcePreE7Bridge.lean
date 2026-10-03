import SymmetricSubgroupAsymptotics.PrimeMarkedRelativeCompleteSourceEnvelope
import SymmetricSubgroupAsymptotics.RelativeCompleteSourcePreE7Bridge
import SymmetricSubgroupAsymptotics.Non2PreE7RankTailSourceDichotomyClosure

/-!
# Prime-marked complete sources at the pre-E7 boundary

An invariant prime radical is retained as same-source character columns and
the quotient action is padded by fixed points.  The total moment degree is
therefore the padded joint degree, while the coefficient keeps the affine
growth class already accepted by the global menu theorem.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimeMarkedRelativeCompleteSourceEnvelope

variable (p : ℕ) [Fact p.Prime]
variable {w : ℕ} {U : PreE7NonPairActionClass w}

/-- Permutation degree occupied jointly by the quotient comparator and all
retained prime-character columns. -/
def jointDegree
    {G : Type} [Group G] [Finite G]
    (E : PrimeMarkedRelativeCompleteSourceEnvelope p G) : ℕ :=
  E.quotientDegree + p * E.markerColumns

/-- Pad only the quotient action, leaving the retained prime columns
literal.  The resulting total degree is the standard padded joint degree. -/
noncomputable def preE7Pad
    (E : PrimeMarkedRelativeCompleteSourceEnvelope p
      (preE7NonPairAction w U)) :
    PrimeMarkedRelativeCompleteSourceEnvelope p
      (preE7NonPairAction w U) := by
  let v := paddedComparatorDegree preE7CharacterRho (jointDegree p E) w
  have hmark : p * E.markerColumns ≤ v := by
    exact (Nat.le_add_left (p * E.markerColumns) E.quotientDegree).trans
      (le_max_left _ _)
  have hquot : E.quotientDegree ≤ v - p * E.markerColumns := by
    apply Nat.le_sub_of_add_le
    simpa only [jointDegree, Nat.add_comm] using
      (le_max_left (jointDegree p E)
        ⌊4 * preE7CharacterRho * (evenWidth w : ℝ)⌋₊)
  exact
    { R := E.R
      groupR := E.groupR
      finiteR := E.finiteR
      quotientDegree := v - p * E.markerColumns
      action := (characterComparatorPadHom hquot).comp E.action
      action_injective :=
        (characterComparatorPadHom_injective hquot).comp E.action_injective
      markerColumns := E.markerColumns
      coefficient := E.coefficient
      eta := E.eta
      coefficient_nonneg := E.coefficient_nonneg
      bound := E.bound }

theorem preE7Pad_jointDegree
    (E : PrimeMarkedRelativeCompleteSourceEnvelope p
      (preE7NonPairAction w U)) :
    jointDegree p (preE7Pad p E) =
      paddedComparatorDegree preE7CharacterRho (jointDegree p E) w := by
  let v := paddedComparatorDegree preE7CharacterRho (jointDegree p E) w
  have hmark : p * E.markerColumns ≤ v := by
    exact (Nat.le_add_left (p * E.markerColumns) E.quotientDegree).trans
      (le_max_left _ _)
  simp only [jointDegree, preE7Pad]
  exact Nat.sub_add_cancel hmark

/-- The genuine numerical obligations for a marked affine row. -/
structure PreE7Margin
    (E : PrimeMarkedRelativeCompleteSourceEnvelope p
      (preE7NonPairAction w U)) : Prop where
  eta_nonneg : 0 ≤ E.eta
  jointDegree_two_le : 2 ≤ jointDegree p E
  margin : preE7CharacterRho * w ≤
    ((evenWidth w : ℝ) - jointDegree p E) / 8 - E.eta
  coefficient_growth : ∀ b,
    E.coefficient b ≤ (2 : ℝ) ^
      (PrimitiveAffineImprimitiveBlockTransfer.affineComponentWidthCost w +
        8 * (w : ℝ) * Real.logb 2 (b + 1))

namespace PreE7Margin

variable
  (E : PrimeMarkedRelativeCompleteSourceEnvelope p
    (preE7NonPairAction w U))
  (M : PreE7Margin p E)

include M

theorem parameters :
    PreE7CharacterEntryParameters preE7CharacterRho w
      (jointDegree p (preE7Pad p E)) E.eta
      (paddedComparatorDelta preE7CharacterRho E.eta
        (jointDegree p E) w)
      ((paddedComparatorDegree preE7CharacterRho (jointDegree p E) w : ℝ) / 8 +
        paddedComparatorDelta preE7CharacterRho E.eta
          (jointDegree p E) w / 2)
      (E.eta +
        ((paddedComparatorDegree preE7CharacterRho (jointDegree p E) w : ℝ) / 8 +
          paddedComparatorDelta preE7CharacterRho E.eta
            (jointDegree p E) w / 2)) 0 := by
  rw [preE7Pad_jointDegree]
  exact preE7Padded_entryParameters M.eta_nonneg M.jointDegree_two_le M.margin

end PreE7Margin

/-- Forgetting the terminal predicate embeds the full physical source in
the complete original quotient weight. -/
theorem terminal_source_le_completeQuotientWeight
    (_E : PrimeMarkedRelativeCompleteSourceEnvelope p
      (preE7NonPairAction w U))
    (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b))) :
    fusionCompleteSourceSum (preE7NonPairAction w U)
        (preE7NoPairNoC3CertifiedFirstOwnerPredicate
          preE7NoPairNoC3EarlierNumericalRankTailFamilyAction w
          (Fin.last preE7NoPairNoC3EarlierOwnerCount, U) b) J ≤
      completeQuotientWeight (R := preE7NonPairAction w U) J := by
  unfold fusionCompleteSourceSum completeQuotientWeight completeQuotientCount
  rw [Nat.cast_sum]
  exact Finset.sum_le_sum (fun N _ ↦
    fusionSurvivingEpiCount_le_groupEpimorphism_card
      (preE7NonPairAction w U)
      (preE7NoPairNoC3CertifiedFirstOwnerPredicate
        preE7NoPairNoC3EarlierNumericalRankTailFamilyAction w
        (Fin.last preE7NoPairNoC3EarlierOwnerCount, U) b) N J)

/-- Install a prime-marked affine envelope as the terminal residual row.
Its main coefficient uses the accepted affine growth class. -/
noncomputable def toResidualChoiceOfMargin
    (E : PrimeMarkedRelativeCompleteSourceEnvelope p
      (preE7NonPairAction w U))
    (M : PreE7Margin p E) :
    PreE7NumericalRankTailResidualChoice w U := by
  let E' := preE7Pad p E
  let delta := paddedComparatorDelta preE7CharacterRho E.eta
    (jointDegree p E) w
  let cutoff :=
    (paddedComparatorDegree preE7CharacterRho (jointDegree p E) w : ℝ) / 8 +
      delta / 2
  refine
    { D := E'.coefficient
      v := jointDegree p E'
      eta := E'.eta
      delta := delta
      cutoff := cutoff
      alpha := E'.eta + cutoff
      theta := 0
      X := 0
      alpha_eq := rfl
      D_nonneg := E'.coefficient_nonneg
      parameters := ?_
      main_total_growth := .inr ?_
      exceptional := fun _ ↦
        { threshold := 0
          rate := 1
          constant := 1
          rate_pos := by norm_num
          constant_pos := by norm_num
          bound := by simp }
      exceptional_support := Or.inl rfl
      local_bound := ?_ }
  · simpa only [E', delta, cutoff, preE7Pad] using M.parameters p E
  · intro b
    simpa only [E', preE7Pad] using M.coefficient_growth b
  · intro b
    let P := preE7NoPairNoC3CertifiedFirstOwnerPredicate
      preE7NoPairNoC3EarlierNumericalRankTailFamilyAction w
      (Fin.last preE7NoPairNoC3EarlierOwnerCount, U) b
    have h := E'.physical_kernel_bound p
      (preE7NonPairAction w U) P
      (preE7NoPairNoC3CertifiedFirstOwnerPredicate_natural _ w
        (Fin.last preE7NoPairNoC3EarlierOwnerCount, U) b)
      (terminal_source_le_completeQuotientWeight p E' b)
      delta cutoff
    simpa only [P, E', delta, cutoff, jointDegree, Pi.zero_apply,
      add_zero] using h

end PrimeMarkedRelativeCompleteSourceEnvelope
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
