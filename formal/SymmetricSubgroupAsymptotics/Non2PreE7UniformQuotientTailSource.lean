import SymmetricSubgroupAsymptotics.Non2PreE7CompleteSourceRankTailBridge
import SymmetricSubgroupAsymptotics.Non2PreE7PaddedCertificateNumerics

/-!
# Uniform quotient tails as complete pre-E7 sources

Several finite affine-frame arguments give the same kind of conclusion on
every literal normal quotient of an ambient action: the number of onto maps
is bounded by a fixed coefficient times one cold exponential.  This file
sums those coefficients before entering the physical transfer.  Thus the
normal-axis menu is paid once and no fictitious pointwise comparator is
introduced.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

private abbrev NormalAxis {w : ℕ} (U : PreE7NonPairActionClass w) :=
  {N : Subgroup (preE7NonPairAction w U) // N.Normal}

/-- From width four onward, a two-point trivial seed has the padding margin
required by the pre-E7 transfer. -/
theorem preE7_trivialSeed_margin {w : ℕ} (hw : 4 ≤ w) :
    preE7CharacterRho * w ≤ ((evenWidth w : ℝ) - 2) / 8 := by
  have hwR : (4 : ℝ) ≤ w := by exact_mod_cast hw
  have heven : (w : ℝ) - 1 ≤ (evenWidth w : ℝ) := by
    have h := width_le_evenWidth_add_one w
    have h' : (w : ℝ) ≤ (evenWidth w : ℝ) + 1 := by exact_mod_cast h
    linarith
  unfold preE7CharacterRho
  norm_num
  linarith

/-- A cold quotient envelope on every literal normal axis of one retained
action.  Its coefficient total is required in the same subquadratic form
used by all complete-source certificates. -/
structure PreE7UniformQuotientTailSourceData
    (family : PreE7NoPairNoC3EarlierOwnerFamily)
    (w : ℕ) (U : PreE7NonPairActionClass w) : Type where
  width_lower : 4 ≤ w
  theta : ℝ
  theta_window : theta ≤ preE7CharacterWindow w
  coefficient : NormalAxis U → ℝ
  coefficient_nonneg : ∀ N, 0 ≤ coefficient N
  quotient_bound : ∀ (N : NormalAxis U) (b : ℕ)
      (J : Subgroup (Equiv.Perm (Fin b))),
    (Nat.card (GroupEpimorphism J
        (preE7NonPairAction w U ⧸ N.1)) : ℝ) ≤
      coefficient N * (2 : ℝ) ^ (theta * b)
  coefficient_total_bound : ∀ b,
    fusionAxisEnvelopeTotal (preE7NonPairAction w U) coefficient ≤
      (2 : ℝ) ^
        (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2)

namespace PreE7UniformQuotientTailSourceData

variable {family : PreE7NoPairNoC3EarlierOwnerFamily}
  {w : ℕ} {U : PreE7NonPairActionClass w}
  (D : PreE7UniformQuotientTailSourceData family w U)

/-- The normal-axis coefficient, summed before the physical transfer. -/
def totalCoefficient : ℝ :=
  fusionAxisEnvelopeTotal (preE7NonPairAction w U) D.coefficient

theorem totalCoefficient_nonneg : 0 ≤ D.totalCoefficient := by
  unfold totalCoefficient
  exact fusionAxisEnvelopeTotal_nonneg _ _ D.coefficient_nonneg

/-- The literal broad source is bounded by the sum of the supplied quotient
tails. -/
theorem broad_source_envelope (b : ℕ)
    (J : Subgroup (Equiv.Perm (Fin b))) :
    fusionCompleteSourceSum (preE7NonPairAction w U)
        (preE7NoPairNoC3BroadActionPredicate w U b) J ≤
      D.totalCoefficient * (2 : ℝ) ^ (D.theta * b) := by
  apply fusionCompleteSourceSum_le_axisEnvelopeTotal
    (preE7NonPairAction w U)
    (preE7NoPairNoC3BroadActionPredicate w U b)
    D.coefficient (fun _ => (2 : ℝ) ^ (D.theta * b))
  intro N K
  exact (fusionSurvivingEpiCount_le_groupEpimorphism_card
    (preE7NonPairAction w U)
    (preE7NoPairNoC3BroadActionPredicate w U b) N K).trans
      (D.quotient_bound N b K)

/-- The complete-source certificate with a trivial comparator and one pure
cold row. -/
noncomputable def certificate :
    PreE7CompleteSourceComparatorCertificate family w U := by
  let v := paddedComparatorDegree preE7CharacterRho 2 w
  let delta := paddedComparatorDelta preE7CharacterRho 0 2 w
  let cutoff := (v : ℝ) / 8 + delta / 2
  exact
    { R := PUnit
      groupR := inferInstance
      finiteR := inferInstance
      v := v
      action := 1
      action_injective := fun _ _ _ => Subsingleton.elim _ _
      D := fun _ => 0
      T := fun _ => D.totalCoefficient
      eta := 0
      delta := delta
      cutoff := cutoff
      alpha := cutoff
      theta := D.theta
      alpha_eq := by simp
      D_nonneg := fun _ => le_rfl
      T_nonneg := fun _ => D.totalCoefficient_nonneg
      broad_source_envelope := by
        intro b J
        rw [completeQuotientWeight_eq_one_of_subsingleton (R := PUnit) J]
        simpa using D.broad_source_envelope b J }

/-- Every transfer parameter is forced by the standard two-point padding
and the supplied cold-window inequality. -/
theorem parameters :
    PreE7CharacterEntryParameters preE7CharacterRho w
      D.certificate.v D.certificate.eta D.certificate.delta
      D.certificate.cutoff D.certificate.alpha D.certificate.theta := by
  simpa [certificate] using
    (preE7Padded_entryParameters_withTail
      (w := w) (v0 := 2) (eta := (0 : ℝ)) (theta := D.theta)
      (by norm_num) (by norm_num)
      (by simpa using preE7_trivialSeed_margin D.width_lower)
      D.theta_window)

/-- The quotient-tail source is a complete numerical earlier-owner source. -/
noncomputable def numericalData :
    PreE7CompleteSourceNumericalData family w U where
  certificate := D.certificate
  parameters := D.parameters
  main_total_bound := fun _ => by
    change (0 : ℝ) ≤ _
    positivity
  tail_total_bound := by
    intro b
    change D.totalCoefficient ≤ _
    exact D.coefficient_total_bound b

/-- Final rank-tail source exported to the affine exceptional-cell
consumer. -/
noncomputable def toRankTailSourceOrYonedaTop :
    PreE7RankTailSourceOrYonedaTopData w U :=
  .inl D.numericalData.toRankTailOwnerSource

end PreE7UniformQuotientTailSourceData

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
