import SymmetricSubgroupAsymptotics.RelativeCompleteSourceEnvelope
import SymmetricSubgroupAsymptotics.Non2PreE7CompleteSourceRankTailBridge
import SymmetricSubgroupAsymptotics.Non2PreE7PaddedCertificateNumerics

/-!
# A relative complete-source envelope at the pre-E7 boundary

The local-chief tower bounds the complete sum over every literal normal
quotient of the original action.  This file proves that this is already the
complete-source certificate consumed by the numerical pre-E7 catalogue.
The broad survival predicate only decreases that complete sum.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

variable {w : ℕ} {U : PreE7NonPairActionClass w}

/-- The numerical facts attached to a relative complete-source envelope.
They contain no group-theoretic transfer: that transfer is the `bound` field
of the envelope and is proved by the actual wreath-compression tower. -/
structure RelativeCompleteSourcePreE7Numerics
    (E : RelativeCompleteSourceEnvelope (preE7NonPairAction w U)) : Type where
  delta : ℝ
  cutoff : ℝ
  alpha : ℝ
  theta : ℝ
  alpha_eq : alpha = E.eta + cutoff
  parameters : PreE7CharacterEntryParameters preE7CharacterRho w E.v E.eta
    delta cutoff alpha theta
  coefficient_bound : ∀ b,
    E.coefficient b ≤
      (2 : ℝ) ^
        (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2)

namespace RelativeCompleteSourceEnvelope

/-- Pad the faithful terminal comparator by fixed points.  This changes
neither the comparator group nor any complete-source weight; it only gives
the moment argument enough visible degree at the ambient width. -/
noncomputable def pad
    (E : RelativeCompleteSourceEnvelope (preE7NonPairAction w U))
    (v : ℕ) (hv : E.v ≤ v) :
    RelativeCompleteSourceEnvelope (preE7NonPairAction w U) where
  R := E.R
  groupR := E.groupR
  finiteR := E.finiteR
  v := v
  action := (characterComparatorPadHom hv).comp E.action
  action_injective :=
    (characterComparatorPadHom_injective hv).comp E.action_injective
  coefficient := E.coefficient
  eta := E.eta
  coefficient_nonneg := E.coefficient_nonneg
  bound := E.bound

/-- The controlled pre-E7 padding of a relative envelope. -/
noncomputable def preE7Pad
    (E : RelativeCompleteSourceEnvelope (preE7NonPairAction w U)) :
    RelativeCompleteSourceEnvelope (preE7NonPairAction w U) :=
  pad E (paddedComparatorDegree preE7CharacterRho E.v w)
    (le_max_left _ _)

/-- Construction-facing numerical input for an actual relative envelope.
Unlike `RelativeCompleteSourcePreE7Numerics`, this asks only for the two
mathematical estimates proved by the component source: the unpadded
linear margin and the subquadratic finite coefficient.  All twelve transfer
parameters are derived below from the standard padding theorem. -/
structure PreE7Margin
    (E : RelativeCompleteSourceEnvelope (preE7NonPairAction w U)) : Prop where
  eta_nonneg : 0 ≤ E.eta
  seedDegree_two_le : 2 ≤ E.v
  margin : preE7CharacterRho * w ≤
    ((evenWidth w : ℝ) - E.v) / 8 - E.eta
  coefficient_bound : ∀ b,
    E.coefficient b ≤
      (2 : ℝ) ^
        (PrimitiveAffineImprimitiveBlockTransfer.affineComponentWidthCost w +
          8 * (w : ℝ) * Real.logb 2 (b + 1))

namespace PreE7Margin

variable (E : RelativeCompleteSourceEnvelope (preE7NonPairAction w U))
  (M : PreE7Margin E)

include M

/-- The standard padding theorem derives every moment parameter; the
construction does not receive those parameters as source data. -/
theorem parameters :
    PreE7CharacterEntryParameters preE7CharacterRho w
      (preE7Pad E).v (preE7Pad E).eta
      (paddedComparatorDelta preE7CharacterRho E.eta E.v w)
      ((paddedComparatorDegree preE7CharacterRho E.v w : ℝ) / 8 +
        paddedComparatorDelta preE7CharacterRho E.eta E.v w / 2)
      (E.eta +
        ((paddedComparatorDegree preE7CharacterRho E.v w : ℝ) / 8 +
          paddedComparatorDelta preE7CharacterRho E.eta E.v w / 2))
      0 := by
  simpa only [preE7Pad, pad] using
    (preE7Padded_entryParameters
      (w := w) (v0 := E.v) (eta := E.eta)
      M.eta_nonneg M.seedDegree_two_le M.margin)

end PreE7Margin

/-- Forgetting the survival predicate embeds the broad physical source in
the complete original normal-axis weight. -/
theorem broad_source_le_completeQuotientWeight
    (_E : RelativeCompleteSourceEnvelope (preE7NonPairAction w U))
    (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b))) :
    fusionCompleteSourceSum (preE7NonPairAction w U)
        (preE7NoPairNoC3BroadActionPredicate w U b) J ≤
      completeQuotientWeight (R := preE7NonPairAction w U) J := by
  unfold fusionCompleteSourceSum completeQuotientWeight completeQuotientCount
  rw [Nat.cast_sum]
  exact Finset.sum_le_sum (fun N _ ↦
    fusionSurvivingEpiCount_le_groupEpimorphism_card
      (preE7NonPairAction w U)
      (preE7NoPairNoC3BroadActionPredicate w U b) N J)

/-- Install the exact complete-source transfer furnished by a local-chief
tower as one ordinary numerical owner. -/
noncomputable def toCompleteSourceNumericalData
    (family : PreE7NoPairNoC3EarlierOwnerFamily)
    (E : RelativeCompleteSourceEnvelope (preE7NonPairAction w U))
    (N : RelativeCompleteSourcePreE7Numerics E) :
    PreE7CompleteSourceNumericalData family w U where
  certificate :=
    { R := E.R
      groupR := E.groupR
      finiteR := E.finiteR
      v := E.v
      action := E.action
      action_injective := E.action_injective
      D := E.coefficient
      T := fun _ ↦ 0
      eta := E.eta
      delta := N.delta
      cutoff := N.cutoff
      alpha := N.alpha
      theta := N.theta
      alpha_eq := N.alpha_eq
      D_nonneg := E.coefficient_nonneg
      T_nonneg := fun _ ↦ le_rfl
      broad_source_envelope := by
        intro b J
        calc
          fusionCompleteSourceSum (preE7NonPairAction w U)
              (preE7NoPairNoC3BroadActionPredicate w U b) J ≤
              completeQuotientWeight (R := preE7NonPairAction w U) J :=
            broad_source_le_completeQuotientWeight E b J
          _ ≤ E.coefficient b * (2 : ℝ) ^ (E.eta * b) *
              completeQuotientWeight (R := E.R) J := E.bound b J
          _ = (E.coefficient b * (2 : ℝ) ^ (E.eta * b)) *
                completeQuotientWeight (R := E.R) J +
              0 * (2 : ℝ) ^ (N.theta * b) := by simp }
  parameters := N.parameters
  main_total_bound := N.coefficient_bound
  tail_total_bound := fun _ ↦ by positivity

/-- Direct construction-facing output used by primitive-affine block
transfer. -/
noncomputable def toRankTailSourceOrYonedaTop
    (family : PreE7NoPairNoC3EarlierOwnerFamily)
    (E : RelativeCompleteSourceEnvelope (preE7NonPairAction w U))
    (N : RelativeCompleteSourcePreE7Numerics E) :
    PreE7RankTailSourceOrYonedaTopData w U :=
  .inl ((toCompleteSourceNumericalData family E N).toRankTailOwnerSource)

/-- Direct source construction from the two genuine component estimates.
The comparator is padded only after the exact complete-source transfer has
been proved. -/
noncomputable def toRankTailSourceOrYonedaTopOfMargin
    (family : PreE7NoPairNoC3EarlierOwnerFamily)
    (E : RelativeCompleteSourceEnvelope (preE7NonPairAction w U))
    (M : PreE7Margin E) :
    PreE7RankTailSourceOrYonedaTopData w U := by
  let E' := preE7Pad E
  let delta := paddedComparatorDelta preE7CharacterRho E.eta E.v w
  let cutoff := (paddedComparatorDegree preE7CharacterRho E.v w : ℝ) / 8 +
    delta / 2
  let alpha := E.eta + cutoff
  let C : PreE7CompleteSourceComparatorCertificate family w U :=
    { R := E'.R
      groupR := E'.groupR
      finiteR := E'.finiteR
      v := E'.v
      action := E'.action
      action_injective := E'.action_injective
      D := E'.coefficient
      T := fun _ ↦ 0
      eta := E'.eta
      delta := delta
      cutoff := cutoff
      alpha := alpha
      theta := 0
      alpha_eq := rfl
      D_nonneg := E'.coefficient_nonneg
      T_nonneg := fun _ ↦ le_rfl
      broad_source_envelope := by
        intro b J
        calc
          fusionCompleteSourceSum (preE7NonPairAction w U)
              (preE7NoPairNoC3BroadActionPredicate w U b) J ≤
              completeQuotientWeight (R := preE7NonPairAction w U) J :=
            broad_source_le_completeQuotientWeight E' b J
          _ ≤ E'.coefficient b * (2 : ℝ) ^ (E'.eta * b) *
              completeQuotientWeight (R := E'.R) J := E'.bound b J
          _ = (E'.coefficient b * (2 : ℝ) ^ (E'.eta * b)) *
                completeQuotientWeight (R := E'.R) J +
              0 * (2 : ℝ) ^ ((0 : ℝ) * b) := by simp }
  let package : PreE7EarlierNumericalPackage family w U :=
    .ofAffinePackage C.localPackage (by
      simpa only [E', delta, cutoff, alpha] using M.parameters E) (by
      intro b
      simpa only [E', preE7Pad, pad] using M.coefficient_bound b) (by
      intro b
      change (0 : ℝ) ≤ _
      positivity)
  exact .inl (.ordinary family (.package package))

end RelativeCompleteSourceEnvelope
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
