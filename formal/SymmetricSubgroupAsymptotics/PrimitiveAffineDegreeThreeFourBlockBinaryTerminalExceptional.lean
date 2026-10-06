import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockBinaryTerminalAggregation

/-!
# Exceptional installation of the terminal binary four-block carrier sum

The positive carrier completion is a global negligible-family theorem.  It
should therefore enter the final numerical catalogue as the exceptional
scalar itself, rather than being forced through an artificial fixed
quotient comparator.  This file gives that exact bridge.

The raw scalar below is still the correlated literal-axis sum: direct cells
retain their original weights and positive cells retain the carrier selected
on the same top normal as the elementary contribution.  The only remaining
input is exponential decay of this one scalar, together with the actual
earlier owner on the critical `E8` route.
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

/-- The exact terminal direct/positive cost, summed over complete sources
and the literal signed-quotient top normals. -/
def degreeThreeFourBlockBinaryTerminalRaw
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (b : ℕ) : ℝ :=
  ∑ J : Subgroup (Equiv.Perm (Fin b)),
    ∑ D : {D : Subgroup
        (preE7NonPairAction w U ⧸ E block P) // D.Normal},
      degreeThreeFourBlockBinaryTerminalCellBound
        block P hr hs hcomponent hbinary b J D

theorem degreeThreeFourBlockBinaryTerminalRaw_nonneg
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (b : ℕ) :
    0 ≤ degreeThreeFourBlockBinaryTerminalRaw
      block P hr hs hcomponent hbinary b := by
  unfold degreeThreeFourBlockBinaryTerminalRaw
  exact Finset.sum_nonneg (fun J _ ↦ Finset.sum_nonneg (fun D _ ↦
    degreeThreeFourBlockBinaryTerminalCellBound_nonneg
      block P hr hs hcomponent hbinary b J D))

/-- The physical pointing factor is attached exactly once, after the
correlated complete-source sum. -/
def degreeThreeFourBlockBinaryTerminalNormalized
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (b : ℕ) : ℝ :=
  growingQuotientNormalizedPointing b w
      (Nat.card (Subgroup.normalizer
        (preE7NonPairAction w U : Set (Equiv.Perm (Fin w)))) : ℝ) *
    degreeThreeFourBlockBinaryTerminalRaw
      block P hr hs hcomponent hbinary b

/-- Four blocks of affine degree three have ambient width twelve. -/
theorem degreeThreeFourBlockBinary_width_eq_twelve
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4) : w = 12 := by
  calc
    w = Nat.card block.Fibre * Nat.card block.Points := width_eq block
    _ = 3 * 4 := by rw [hr, hs]
    _ = 12 := by norm_num

/-- Minimal global carrier input.  It contains no extra comparator or
separate maxima: the exceptional theorem sees the complete correlated raw
sum defined above. -/
structure DegreeThreeFourBlockBinaryTerminalExceptionalData
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action) : Type 1 where
  criticalOwner : DegreeThreeFourBlockBinaryCriticalOwnerData
    block P hr hs hcomponent hbinary
  exponential : FusionCoarseEstimate (fun n ↦ (subgroupCount n : ℝ)) →
    ExponentialScalarBound
      (degreeThreeFourBlockBinaryTerminalNormalized
        block P hr hs hcomponent hbinary)

namespace DegreeThreeFourBlockBinaryTerminalExceptionalData

variable
  {hr : Nat.card block.Fibre = 3}
  {hs : Nat.card block.Points = 4}
  {hcomponent : Nat.card block.Component = 6}
  {hbinary : IsPGroup 2
    (degreeThreeFourBlockPairChart block P hr hs hcomponent).action}
  (X : DegreeThreeFourBlockBinaryTerminalExceptionalData
    block P hr hs hcomponent hbinary)

/-- Put a globally negligible carrier sector into the exceptional slot of
the terminal aggregate.  The main and additive-tail rows are identically
zero. -/
noncomputable def toTerminalAggregate :
    DegreeThreeFourBlockBinaryTerminalAggregate
      block P hr hs hcomponent hbinary where
  criticalOwner := X.criticalOwner
  R := PUnit
  groupR := inferInstance
  finiteR := inferInstance
  v := preE7EmptyCellDegree w
  action := 1
  action_injective := fun _ _ _ ↦ Subsingleton.elim _ _
  D := fun _ ↦ 0
  T := fun _ ↦ 0
  eta := 0
  theta := 0
  delta := preE7EmptyCellDelta w
  cutoff := preE7EmptyCellCutoff w
  alpha := preE7EmptyCellAlpha w
  rawExceptional := degreeThreeFourBlockBinaryTerminalRaw
    block P hr hs hcomponent hbinary
  alpha_eq := by simp [preE7EmptyCellAlpha]
  D_nonneg := fun _ ↦ le_rfl
  T_nonneg := fun _ ↦ le_rfl
  T_le_D := fun _ ↦ le_rfl
  rawExceptional_nonneg :=
    degreeThreeFourBlockBinaryTerminalRaw_nonneg
      block P hr hs hcomponent hbinary
  width_upper := by
    rw [degreeThreeFourBlockBinary_width_eq_twelve block hr hs]
    norm_num
  parameters := preE7EmptyCell_entryParameters
    (preE7NonPairAction_width_three_le U)
  total_growth := fun _ ↦ by positivity
  aggregate := fun b ↦ by
    simp [degreeThreeFourBlockBinaryTerminalRaw]
  exceptional := by
    intro hcoarse
    change ExponentialScalarBound
      (degreeThreeFourBlockBinaryTerminalNormalized
        block P hr hs hcomponent hbinary)
    exact X.exponential hcoarse

end DegreeThreeFourBlockBinaryTerminalExceptionalData

/-- Exact construction theorem after the installation above: prove decay of
the correlated terminal carrier family and route critical `E8` to an actual
earlier owner. -/
abbrev DegreeThreeFourBlockBinaryTerminalExceptionalTheorem :=
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
    Nonempty (DegreeThreeFourBlockBinaryTerminalExceptionalData
      block P hr hs hcomponent hbinary)

/-- The exceptional theorem is already sufficient for the construction
boundary used by the degree-three residual assembly. -/
noncomputable def degreeThreeFourBlockBinaryResidualSource_of_terminalExceptional
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (exceptional : DegreeThreeFourBlockBinaryTerminalExceptionalTheorem) :
    DegreeThreeFourBlockBinaryResidualSource :=
  degreeThreeFourBlockBinaryResidualSource_of_terminalCapacity
    hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm (by
      intro w U basePoint block P _inst hr hs hcomponent hK hbinary
      let X := Classical.choice
        (exceptional U basePoint block P hr hs hcomponent hK hbinary)
      exact ⟨X.toTerminalAggregate block P⟩)

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
