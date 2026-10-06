import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockBinaryTerminalExceptional

/-!
# Exact exceptional installation for the binary four-block affine cell

The first terminal exceptional interface enlarged every positive carrier
fibre to the product of a complete carrier quotient moment and an elementary
top contribution.  That enlargement is valid locally, but it discards the
correlation needed at the width-twelve numerical boundary.  In particular,
its two separate worst-case exponents do not fit the available width budget.

This file keeps the accepted positive fibre literally unchanged.  Direct
axes still use their proved original-weight estimate, and critical `E8` axes
are still removed by an actual earlier owner.  Thus the sole remaining
analytic input is exponential decay of the exact accepted positive family;
it can be proved by a reversible carrier construction without first paying
two independent maxima.
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

/-- The route-selected cost on one literal top, without relaxing a positive
carrier fibre.  This is the correct object for the final reversible-carrier
theorem. -/
def degreeThreeFourBlockBinaryExactTerminalCell
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b)))
    (D : {D : Subgroup
      (preE7NonPairAction w U ⧸ E block P) // D.Normal}) : ℝ :=
  match degreeThreeFourBlockBinaryCertifiedAxisChoice
      block P hr hs hcomponent hbinary D with
  | .direct A =>
      ((2 : ℝ) ^ (384 : ℝ) * (3 : ℝ) ^ ((b : ℝ) / 3)) *
        (fusionLocalFactor b 4 A.prefixDegree A.liftConstant A.gapParameter *
          A.momentWeight J)
  | .positive _ =>
      degreeThreeFourBlockBinaryAcceptedTopTerm block P
        (degreeThreeFourBlockBinaryTerminalPredicate (U := U) b) J D
  | .criticalE8 _ => 0

theorem degreeThreeFourBlockBinaryExactTerminalCell_nonneg
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b)))
    (D : {D : Subgroup
      (preE7NonPairAction w U ⧸ E block P) // D.Normal}) :
    0 ≤ degreeThreeFourBlockBinaryExactTerminalCell
      block P hr hs hcomponent hbinary b J D := by
  cases hchoice : degreeThreeFourBlockBinaryCertifiedAxisChoice
      block P hr hs hcomponent hbinary D with
  | direct A =>
      simp only [degreeThreeFourBlockBinaryExactTerminalCell, hchoice]
      apply mul_nonneg
        (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
          (Real.rpow_nonneg (by norm_num) _))
      exact (Nat.cast_nonneg _).trans
        (degreeThreeFourBlockBinary_directAxis_epi_le
          block P hr hs hcomponent D A J)
  | positive R =>
      simp only [degreeThreeFourBlockBinaryExactTerminalCell, hchoice]
      unfold degreeThreeFourBlockBinaryAcceptedTopTerm
      exact Finset.sum_nonneg (fun N _ ↦ Nat.cast_nonneg _)
  | criticalE8 hE8 =>
      simp only [degreeThreeFourBlockBinaryExactTerminalCell, hchoice]
      exact le_rfl

/-- Accepted tops are charged directly on positive routes, by the proved
original-weight row on direct routes, and by zero after the critical owner
has accepted the ambient action. -/
theorem degreeThreeFourBlockBinaryAcceptedTopTerm_le_exactTerminalCell
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (criticalOwner : DegreeThreeFourBlockBinaryCriticalOwnerData
      block P hr hs hcomponent hbinary)
    (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b)))
    (D : {D : Subgroup
      (preE7NonPairAction w U ⧸ E block P) // D.Normal}) :
    degreeThreeFourBlockBinaryAcceptedTopTerm block P
        (degreeThreeFourBlockBinaryTerminalPredicate (U := U) b) J D ≤
      degreeThreeFourBlockBinaryExactTerminalCell
        block P hr hs hcomponent hbinary b J D := by
  cases hchoice : degreeThreeFourBlockBinaryCertifiedAxisChoice
      block P hr hs hcomponent hbinary D with
  | direct A =>
      simpa only [degreeThreeFourBlockBinaryExactTerminalCell, hchoice] using
        degreeThreeFourBlockBinaryAcceptedTopTerm_direct_le block P
          hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
          hr hs hcomponent hbinary
          (degreeThreeFourBlockBinaryTerminalPredicate (U := U) b) D A J
  | positive R =>
      simp only [degreeThreeFourBlockBinaryExactTerminalCell, hchoice]
      exact le_rfl
  | criticalE8 hE8 =>
      rw [degreeThreeFourBlockBinaryAcceptedTopTerm_eq_zero_of_actionOwner
        block P (criticalOwner D hE8) J D]
      simp only [degreeThreeFourBlockBinaryExactTerminalCell, hchoice]
      exact le_rfl

/-- Exact terminal raw count.  The positive summands are the surviving
accepted fibres themselves, not a product of independently enlarged terms. -/
def degreeThreeFourBlockBinaryExactTerminalRaw
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (b : ℕ) : ℝ :=
  ∑ J : Subgroup (Equiv.Perm (Fin b)),
    ∑ D : {D : Subgroup
        (preE7NonPairAction w U ⧸ E block P) // D.Normal},
      degreeThreeFourBlockBinaryExactTerminalCell
        block P hr hs hcomponent hbinary b J D

theorem degreeThreeFourBlockBinaryExactTerminalRaw_nonneg
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (b : ℕ) :
    0 ≤ degreeThreeFourBlockBinaryExactTerminalRaw
      block P hr hs hcomponent hbinary b := by
  unfold degreeThreeFourBlockBinaryExactTerminalRaw
  exact Finset.sum_nonneg (fun J _ ↦ Finset.sum_nonneg (fun D _ ↦
    degreeThreeFourBlockBinaryExactTerminalCell_nonneg
      block P hr hs hcomponent hbinary b J D))

/-- The terminal complete source, summed over every source, is bounded by
the exact correlated raw count. -/
theorem degreeThreeFourBlockBinaryTerminalSummed_le_exactTerminalRaw
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (criticalOwner : DegreeThreeFourBlockBinaryCriticalOwnerData
      block P hr hs hcomponent hbinary)
    (b : ℕ) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)),
      fusionCompleteSourceSum (preE7NonPairAction w U)
        (degreeThreeFourBlockBinaryTerminalPredicate (U := U) b) J) ≤
      degreeThreeFourBlockBinaryExactTerminalRaw
        block P hr hs hcomponent hbinary b := by
  unfold degreeThreeFourBlockBinaryExactTerminalRaw
  apply Finset.sum_le_sum
  intro J _hJ
  rw [degreeThreeFourBlockBinary_completeSourceSum_eq_acceptedTop block P]
  exact Finset.sum_le_sum (fun D _ ↦
    degreeThreeFourBlockBinaryAcceptedTopTerm_le_exactTerminalCell
      block P hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
      hr hs hcomponent hbinary criticalOwner b J D)

/-- Physical pointing is attached once, after the exact correlated sum. -/
def degreeThreeFourBlockBinaryExactTerminalNormalized
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (b : ℕ) : ℝ :=
  growingQuotientNormalizedPointing b w
      (Nat.card (Subgroup.normalizer
        (preE7NonPairAction w U : Set (Equiv.Perm (Fin w)))) : ℝ) *
    degreeThreeFourBlockBinaryExactTerminalRaw
      block P hr hs hcomponent hbinary b

/-- The corrected final analytic datum.  Its exponential field is precisely
the reversible-carrier theorem still to be proved; no relaxed positive-cell
product occurs in its statement. -/
structure DegreeThreeFourBlockBinaryExactTerminalExceptionalData
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action) : Type 1 where
  criticalOwner : DegreeThreeFourBlockBinaryCriticalOwnerData
    block P hr hs hcomponent hbinary
  exponential : FusionCoarseEstimate (fun n ↦ (subgroupCount n : ℝ)) →
    ExponentialScalarBound
      (degreeThreeFourBlockBinaryExactTerminalNormalized
        block P hr hs hcomponent hbinary)

namespace DegreeThreeFourBlockBinaryExactTerminalExceptionalData

variable
  {hr : Nat.card block.Fibre = 3}
  {hs : Nat.card block.Points = 4}
  {hcomponent : Nat.card block.Component = 6}
  {hbinary : IsPGroup 2
    (degreeThreeFourBlockPairChart block P hr hs hcomponent).action}
  (X : DegreeThreeFourBlockBinaryExactTerminalExceptionalData
    block P hr hs hcomponent hbinary)

/-- Install the exact raw family directly into the exceptional slot.  This
does not pass through `DegreeThreeFourBlockBinaryTerminalAggregate`, whose
left side is the relaxed positive-cell product. -/
noncomputable def residualChoice
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput) :
    PreE7NumericalRankTailResidualChoice w U where
  D := fun _ ↦ 0
  T := fun _ ↦ 0
  v := preE7EmptyCellDegree w
  eta := 0
  delta := preE7EmptyCellDelta w
  cutoff := preE7EmptyCellCutoff w
  alpha := preE7EmptyCellAlpha w
  theta := 0
  X := degreeThreeFourBlockBinaryExactTerminalNormalized
    block P hr hs hcomponent hbinary
  alpha_eq := by simp [preE7EmptyCellAlpha]
  D_nonneg := fun _ ↦ le_rfl
  T_nonneg := fun _ ↦ le_rfl
  T_le_D := fun _ ↦ le_rfl
  parameters := preE7EmptyCell_entryParameters
    (preE7NonPairAction_width_three_le U)
  main_total_growth := .inl (fun _ ↦ by positivity)
  exceptional := X.exponential
  exceptional_support := Or.inr (by
    rw [degreeThreeFourBlockBinary_width_eq_twelve block hr hs]
    norm_num)
  local_bound := by
    intro b
    let source := degreeThreeFourBlockBinaryTerminalPredicate (U := U) b
    have h :=
      fusionPhysical_growingQuotient_additiveTail_summedExceptional_kernel_bound
        (preE7NonPairAction w U) source
        (preE7NoPairNoC3CertifiedFirstOwnerPredicate_natural _ w
          (Fin.last preE7NoPairNoC3EarlierOwnerCount, U) b)
        (1 : Unit →* Equiv.Perm (Fin (preE7EmptyCellDegree w)))
        (fun (x y : Unit) (_h : (1 : Unit →* Equiv.Perm (Fin (preE7EmptyCellDegree w))) x =
            (1 : Unit →* Equiv.Perm (Fin (preE7EmptyCellDegree w))) y) ↦
          Subsingleton.elim x y)
        0 0 0 0 (preE7EmptyCellDelta w) (preE7EmptyCellCutoff w)
        (degreeThreeFourBlockBinaryExactTerminalRaw
          block P hr hs hcomponent hbinary b) le_rfl
        (by
          simpa only [source, zero_mul, zero_add, Finset.sum_const_zero,
            add_zero] using
            degreeThreeFourBlockBinaryTerminalSummed_le_exactTerminalRaw
              block P hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
              hr hs hcomponent hbinary X.criticalOwner b)
    simpa [source, preE7EmptyCellAlpha,
      degreeThreeFourBlockBinaryExactTerminalNormalized,
      fusionWidthColdKernel, ordinarySubgroupRatio] using h

/-- Final construction-facing source for the corrected exact family. -/
noncomputable def source
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput) :
    PreE7RankTailSourceOrYonedaTopData w U :=
  .inr (.inr (X.residualChoice block P hTraceyHalf hTraceyLog
    hTraceyRefined hTraceyPerm))

end DegreeThreeFourBlockBinaryExactTerminalExceptionalData

/-- Correct final theorem boundary for the binary four-block residual cell. -/
abbrev DegreeThreeFourBlockBinaryExactTerminalExceptionalTheorem :=
  ∀ {w : ℕ} (U : PreE7NonPairActionClass w)
    (basePoint : Fin w)
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (_hK : degreeNineLinearBlockKernel block P ≠ ⊥)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action),
    Nonempty (DegreeThreeFourBlockBinaryExactTerminalExceptionalData
      block P hr hs hcomponent hbinary)

/-- The corrected exceptional theorem fills the degree-three residual source
without assuming decay of the relaxed positive-cell product. -/
noncomputable def degreeThreeFourBlockBinaryResidualSource_of_exactTerminalExceptional
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (exceptional : DegreeThreeFourBlockBinaryExactTerminalExceptionalTheorem) :
    DegreeThreeFourBlockBinaryResidualSource := by
  intro w U _hw basePoint block P _hNT _hres hr hs hcomponent hK hbinary
  exact DegreeThreeFourBlockBinaryExactTerminalExceptionalData.source block P
    (Classical.choice
      (exceptional U basePoint block P hr hs hcomponent hK hbinary))
    hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
