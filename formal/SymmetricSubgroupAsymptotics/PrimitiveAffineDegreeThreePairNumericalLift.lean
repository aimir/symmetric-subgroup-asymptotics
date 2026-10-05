import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeSignedQuotientEndpoint
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeRawExceptionalDecay

/-!
# Additive numerical lift of a raw pair package through the ternary layer

The degree-two package has two genuinely different rows: a complete-quotient
comparator and a source-independent cold tail.  They must keep their own
slopes after the ternary layer is prepended.  In particular the cold tail is
not charged to the comparator degree.  This is the reusable adapter used by
the nonzero signed-kernel residual lane.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

/-- Numerical obligations for the two rows after the literal ternary cost is
added.  `D` is allowed to dominate `T`; this does not merge their exponents,
and lets the global terminal menu charge both coefficient families through
one already controlled menu mass. -/
structure DegreeThreeSignedQuotientAdditiveNumerics
    (H : ElementaryLayerJointCapacityBound
      (elementaryChart block P).p
      (QuotientGroup.mk' (E block P))
      (QuotientGroup.mk'_surjective (E block P))
      (elementaryChart block P).quotientRepresentation
      (elementaryChart block P).originalKernelChart)
    (G : PreE7DegreeTwoPairQuotientGrowthPackage
      (preE7NonPairAction w U ⧸ E block P)) : Type where
  D : ℕ → ℝ
  T : ℕ → ℝ
  eta : ℝ
  theta : ℝ
  delta : ℝ
  cutoff : ℝ
  alpha : ℝ
  alpha_eq : alpha =
    (Real.logb 2 (elementaryChart block P).p /
        (elementaryChart block P).p * H.capacity + eta) + cutoff
  D_nonneg : ∀ b, 0 ≤ D b
  T_nonneg : ∀ b, 0 ≤ T b
  T_le_D : ∀ b, T b ≤ D b
  eta_le : G.package.envelope.eta ≤ eta
  theta_le : G.package.envelope.theta ≤ theta
  mainCoefficient_le : ∀ b,
    H.coefficient * G.package.envelope.mainCoefficient ≤ D b
  coldCoefficient_le : ∀ b,
    H.coefficient * G.package.envelope.coldCoefficient b ≤ T b
  width_upper : w ≤ 12288
  parameters : PreE7CharacterEntryParameters preE7CharacterRho w
    G.package.v
    (Real.logb 2 (elementaryChart block P).p /
        (elementaryChart block P).p * H.capacity + eta)
    delta cutoff alpha
    (Real.logb 2 (elementaryChart block P).p /
        (elementaryChart block P).p * H.capacity + theta)
  total_growth : ∀ b,
    D b ≤ (2 : ℝ) ^
      (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2)

namespace DegreeThreeSignedQuotientAdditiveNumerics

variable
  {H : ElementaryLayerJointCapacityBound
    (elementaryChart block P).p
    (QuotientGroup.mk' (E block P))
    (QuotientGroup.mk'_surjective (E block P))
    (elementaryChart block P).quotientRepresentation
    (elementaryChart block P).originalKernelChart}
  {G : PreE7DegreeTwoPairQuotientGrowthPackage
    (preE7NonPairAction w U ⧸ E block P)}

private theorem additive_cell_le
    (N : DegreeThreeSignedQuotientAdditiveNumerics block P H G)
    (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b))) :
    (((H.coefficient * G.package.envelope.mainCoefficient) *
          (2 : ℝ) ^
            (((Real.logb 2 (elementaryChart block P).p /
                (elementaryChart block P).p * H.capacity) +
                G.package.envelope.eta) * b)) *
          completeQuotientWeight (R := G.package.envelope.R) J +
      (H.coefficient * G.package.envelope.coldCoefficient b) *
          (2 : ℝ) ^
            (((Real.logb 2 (elementaryChart block P).p /
                (elementaryChart block P).p * H.capacity) +
                G.package.envelope.theta) * b)) ≤
      (N.D b * (2 : ℝ) ^
          (((Real.logb 2 (elementaryChart block P).p /
              (elementaryChart block P).p * H.capacity) + N.eta) * b)) *
        completeQuotientWeight (R := G.package.envelope.R) J +
      N.T b * (2 : ℝ) ^
          (((Real.logb 2 (elementaryChart block P).p /
              (elementaryChart block P).p * H.capacity) + N.theta) * b) := by
  let tau : ℝ := Real.logb 2 (elementaryChart block P).p /
    (elementaryChart block P).p * H.capacity
  have hb : (0 : ℝ) ≤ b := by positivity
  have hetaExp :
      (2 : ℝ) ^ ((tau + G.package.envelope.eta) * b) ≤
        (2 : ℝ) ^ ((tau + N.eta) * b) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    apply mul_le_mul_of_nonneg_right _ hb
    linarith [N.eta_le]
  have hthetaExp :
      (2 : ℝ) ^ ((tau + G.package.envelope.theta) * b) ≤
        (2 : ℝ) ^ ((tau + N.theta) * b) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    apply mul_le_mul_of_nonneg_right _ hb
    linarith [N.theta_le]
  have hmain0 : 0 ≤ H.coefficient *
      G.package.envelope.mainCoefficient :=
    mul_nonneg H.coefficient_nonneg
      G.package.envelope.mainCoefficient_nonneg
  have hcold0 : 0 ≤ H.coefficient *
      G.package.envelope.coldCoefficient b :=
    mul_nonneg H.coefficient_nonneg
      (G.package.envelope.coldCoefficient_nonneg b)
  have hZ0 : 0 ≤ completeQuotientWeight
      (R := G.package.envelope.R) J := completeQuotientWeight_nonneg J
  change
    ((H.coefficient * G.package.envelope.mainCoefficient) *
        (2 : ℝ) ^ ((tau + G.package.envelope.eta) * b)) *
          completeQuotientWeight (R := G.package.envelope.R) J +
      (H.coefficient * G.package.envelope.coldCoefficient b) *
        (2 : ℝ) ^ ((tau + G.package.envelope.theta) * b) ≤
      (N.D b * (2 : ℝ) ^ ((tau + N.eta) * b)) *
          completeQuotientWeight (R := G.package.envelope.R) J +
      N.T b * (2 : ℝ) ^ ((tau + N.theta) * b)
  apply add_le_add
  · apply mul_le_mul_of_nonneg_right _ hZ0
    calc
      (H.coefficient * G.package.envelope.mainCoefficient) *
          (2 : ℝ) ^ ((tau + G.package.envelope.eta) * b) ≤
          (H.coefficient * G.package.envelope.mainCoefficient) *
            (2 : ℝ) ^ ((tau + N.eta) * b) :=
        mul_le_mul_of_nonneg_left hetaExp hmain0
      _ ≤ N.D b * (2 : ℝ) ^ ((tau + N.eta) * b) :=
        mul_le_mul_of_nonneg_right (N.mainCoefficient_le b) (by positivity)
  · calc
      (H.coefficient * G.package.envelope.coldCoefficient b) *
          (2 : ℝ) ^ ((tau + G.package.envelope.theta) * b) ≤
          (H.coefficient * G.package.envelope.coldCoefficient b) *
            (2 : ℝ) ^ ((tau + N.theta) * b) :=
        mul_le_mul_of_nonneg_left hthetaExp hcold0
      _ ≤ N.T b * (2 : ℝ) ^ ((tau + N.theta) * b) :=
        mul_le_mul_of_nonneg_right (N.coldCoefficient_le b) (by positivity)

/-- The generic additive certificate on the prepended complete source. -/
noncomputable def margin
    (N : DegreeThreeSignedQuotientAdditiveNumerics block P H G) :
    let S := prependSignedQuotientSummedSource block P H
      G.package.envelope G.package.v G.package.action
        G.package.action_injective
    S.AdditiveNumericalMargin := by
  let tau : ℝ := Real.logb 2 (elementaryChart block P).p /
    (elementaryChart block P).p * H.capacity
  let S := prependSignedQuotientSummedSource block P H
    G.package.envelope G.package.v G.package.action
      G.package.action_injective
  refine
    { D := N.D
      T := N.T
      eta := tau + N.eta
      theta := tau + N.theta
      delta := N.delta
      cutoff := N.cutoff
      alpha := N.alpha
      alpha_eq := ?_
      D_nonneg := N.D_nonneg
      T_nonneg := N.T_nonneg
      T_le_D := N.T_le_D
      width_upper := N.width_upper
      parameters := ?_
      total_growth := N.total_growth
      summed := ?_
      exceptional := prependSignedQuotientGrowth_exceptional block P H G }
  · simpa only [tau] using N.alpha_eq
  · simpa only [tau] using N.parameters
  · intro b source
    have hraw := S.summed b source
    calc
      (∑ J : Subgroup (Equiv.Perm (Fin b)),
          fusionCompleteSourceSum (preE7NonPairAction w U) source J) ≤
          ((∑ J : Subgroup (Equiv.Perm (Fin b)),
            (((H.coefficient * G.package.envelope.mainCoefficient) *
              (2 : ℝ) ^ ((tau + G.package.envelope.eta) * b)) *
                completeQuotientWeight (R := G.package.envelope.R) J +
              (H.coefficient * G.package.envelope.coldCoefficient b) *
                (2 : ℝ) ^ ((tau + G.package.envelope.theta) * b))) +
            S.exceptionalRaw b) := by
        simpa only [S, prependSignedQuotientSummedSource, tau] using hraw
      _ ≤ ((∑ J : Subgroup (Equiv.Perm (Fin b)),
            ((N.D b * (2 : ℝ) ^ ((tau + N.eta) * b)) *
                completeQuotientWeight (R := G.package.envelope.R) J +
              N.T b * (2 : ℝ) ^ ((tau + N.theta) * b))) +
            S.exceptionalRaw b) := by
        exact add_le_add
          (Finset.sum_le_sum (fun J _ => additive_cell_le block P N b J))
          le_rfl

/-- Final source object obtained from a literal pair package without erasing
its additive continuation row. -/
noncomputable def source
    (N : DegreeThreeSignedQuotientAdditiveNumerics block P H G) :
    PreE7RankTailSourceOrYonedaTopData w U := by
  let S := prependSignedQuotientSummedSource block P H
    G.package.envelope G.package.v G.package.action
      G.package.action_injective
  exact .inr (.inr (S.toResidualChoiceAdditive (N.margin block P)))

end DegreeThreeSignedQuotientAdditiveNumerics
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
