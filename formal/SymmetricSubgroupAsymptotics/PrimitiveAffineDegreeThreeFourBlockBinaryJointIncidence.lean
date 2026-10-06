import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockBinaryClosure

/-!
# Branchwise assembly of the binary four-block joint incidence

The scalar attached to a literal top normal is fixed before its degree-eight
classification is inspected.  This file gives the elimination and summation
principle needed by the final proof: a direct entry, a positive carrier slot,
or a critical-E8 witness must bound that same scalar.  The three estimates
are then summed on the literal top axes.  There is no product of an
independently maximized ternary bound with an independently maximized binary
bound.

The final constructor separates this branchwise incidence from the global
numerical row.  Thus the still substantive carrier work has one precise
obligation: produce `cellBound` on the supported slots (and zero on an
already owned critical slot), followed by the displayed single aggregate
inequality.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

open BinaryDegreeEightDirectEntryCoverage
open BinaryDegreeEightPhysicalAnalyticClosure
open BinaryDegreeEightCarrierSourceBridge

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

/-- A bound on the exact joint scalar, proved separately for each payload of
the checked degree-eight classification.  `cellBound` is allowed to depend
on the literal top normal and the exterior source; this is what retains the
annihilator/Yoneda correlation. -/
structure DegreeThreeFourBlockBinaryAxisEnvelope
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action) : Type 2 where
  cellBound : ∀ b,
    Subgroup (Equiv.Perm (Fin b)) →
      {D : Subgroup (preE7NonPairAction w U ⧸ E block P) // D.Normal} → ℝ
  cellBound_nonneg : ∀ b J D, 0 ≤ cellBound b J D
  direct : ∀
    (D : {D : Subgroup
      (preE7NonPairAction w U ⧸ E block P) // D.Normal})
    (A : @DirectEntry8
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action
      (degreeThreeFourBlockBinaryChartAxis block P hr hs hcomponent D.1)
      (degreeThreeFourBlockBinaryChartAxisNormal block P hr hs hcomponent D)),
    degreeThreeFourBlockBinaryAxisChoice block P hr hs hcomponent hbinary D =
      .direct A →
    ∀ (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b))),
      degreeThreeFourBlockBinaryJointTopTerm block P hr hs hcomponent
          hbinary b J D ≤ cellBound b J D
  supported : ∀
    (D : {D : Subgroup
      (preE7NonPairAction w U ⧸ E block P) // D.Normal})
    (S : AxisSlot
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action
      (degreeThreeFourBlockBinaryChartAxis block P hr hs hcomponent D.1)),
    (hS : S.HasNoncritical) →
    degreeThreeFourBlockBinaryAxisChoice block P hr hs hcomponent hbinary D =
      .supported ⟨S, hS⟩ →
    ∀ (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b))),
      degreeThreeFourBlockBinaryJointTopTerm block P hr hs hcomponent
          hbinary b J D ≤ cellBound b J D
  criticalE8 : ∀
    (D : {D : Subgroup
      (preE7NonPairAction w U ⧸ E block P) // D.Normal}),
    (hE8 : IsE8Action
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action) →
    degreeThreeFourBlockBinaryAxisChoice block P hr hs hcomponent hbinary D =
      .criticalE8 hE8 →
    ∀ (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b))),
      degreeThreeFourBlockBinaryJointTopTerm block P hr hs hcomponent
          hbinary b J D ≤ cellBound b J D

namespace DegreeThreeFourBlockBinaryAxisEnvelope

/-- Eliminate the retained classification only after the literal joint
scalar and its proposed cell bound have both been fixed. -/
theorem jointTopTerm_le
    {hr : Nat.card block.Fibre = 3}
    {hs : Nat.card block.Points = 4}
    {hcomponent : Nat.card block.Component = 6}
    {hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action}
    (C : DegreeThreeFourBlockBinaryAxisEnvelope
      block P hr hs hcomponent hbinary)
    (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b)))
    (D : {D : Subgroup
      (preE7NonPairAction w U ⧸ E block P) // D.Normal}) :
    degreeThreeFourBlockBinaryJointTopTerm block P hr hs hcomponent
        hbinary b J D ≤ C.cellBound b J D := by
  cases hchoice : degreeThreeFourBlockBinaryAxisChoice
      block P hr hs hcomponent hbinary D with
  | direct A => exact C.direct D A hchoice b J
  | supported S => exact C.supported D S.1 S.2 hchoice b J
  | criticalE8 hE8 => exact C.criticalE8 D hE8 hchoice b J

/-- Sum the three branch estimates on the same top normals and the same
complete exterior sources. -/
theorem jointSum_le
    {hr : Nat.card block.Fibre = 3}
    {hs : Nat.card block.Points = 4}
    {hcomponent : Nat.card block.Component = 6}
    {hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action}
    (C : DegreeThreeFourBlockBinaryAxisEnvelope
      block P hr hs hcomponent hbinary)
    (b : ℕ) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)),
      ∑ D : {D : Subgroup
          (preE7NonPairAction w U ⧸ E block P) // D.Normal},
        degreeThreeFourBlockBinaryJointTopTerm block P hr hs hcomponent
          hbinary b J D) ≤
      ∑ J : Subgroup (Equiv.Perm (Fin b)),
        ∑ D : {D : Subgroup
            (preE7NonPairAction w U ⧸ E block P) // D.Normal},
          C.cellBound b J D := by
  apply Finset.sum_le_sum
  intro J _
  exact Finset.sum_le_sum (fun D _ ↦
    DegreeThreeFourBlockBinaryAxisEnvelope.jointTopTerm_le
      (block := block) (P := P) C b J D)

end DegreeThreeFourBlockBinaryAxisEnvelope

/-- The only branch estimates not already furnished by the original-weight
direct entry.  These are precisely the positive carrier-cell incidence and
the zero-motion critical-E8 owner implication. -/
structure DegreeThreeFourBlockBinaryNonDirectBounds
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action) : Type 2 where
  supportedValue : ∀
    (D : {D : Subgroup
      (preE7NonPairAction w U ⧸ E block P) // D.Normal}),
    {S : AxisSlot
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action
      (degreeThreeFourBlockBinaryChartAxis block P hr hs hcomponent D.1) //
      S.HasNoncritical} →
    ∀ b, Subgroup (Equiv.Perm (Fin b)) → ℝ
  supported_nonneg : ∀ D S b J, 0 ≤ supportedValue D S b J
  supported_le : ∀ D S b J,
    degreeThreeFourBlockBinaryJointTopTerm block P hr hs hcomponent
        hbinary b J D ≤ supportedValue D S b J
  criticalValue : ∀
    (_D : {D : Subgroup
      (preE7NonPairAction w U ⧸ E block P) // D.Normal}),
    IsE8Action
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action →
    ∀ b, Subgroup (Equiv.Perm (Fin b)) → ℝ
  critical_nonneg : ∀ D hE8 b J, 0 ≤ criticalValue D hE8 b J
  critical_le : ∀ D hE8 b J,
    degreeThreeFourBlockBinaryJointTopTerm block P hr hs hcomponent
        hbinary b J D ≤ criticalValue D hE8 b J

namespace DegreeThreeFourBlockBinaryNonDirectBounds

/-- The selected cell cost.  A direct axis uses its exact original-weight
entry on the same source; only the other two constructors call the remaining
carrier/owner input. -/
def selectedCellBound
    {hr : Nat.card block.Fibre = 3}
    {hs : Nat.card block.Points = 4}
    {hcomponent : Nat.card block.Component = 6}
    {hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action}
    (C : DegreeThreeFourBlockBinaryNonDirectBounds
      block P hr hs hcomponent hbinary)
    (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b)))
    (D : {D : Subgroup
      (preE7NonPairAction w U ⧸ E block P) // D.Normal}) : ℝ :=
  match degreeThreeFourBlockBinaryAxisChoice
      block P hr hs hcomponent hbinary D with
  | .direct A =>
      ((2 : ℝ) ^ (384 : ℝ) * (3 : ℝ) ^ ((b : ℝ) / 3)) *
        (fusionLocalFactor b 4 A.prefixDegree A.liftConstant A.gapParameter *
          A.momentWeight J)
  | .supported S => C.supportedValue D S b J
  | .criticalE8 hE8 => C.criticalValue D hE8 b J

/-- All direct axes are discharged here from the published Tracey inputs.
The resulting envelope exposes only the supported-carrier and critical-E8
branches as mathematical work. -/
noncomputable def toAxisEnvelope
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    {hr : Nat.card block.Fibre = 3}
    {hs : Nat.card block.Points = 4}
    {hcomponent : Nat.card block.Component = 6}
    {hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action}
    (C : DegreeThreeFourBlockBinaryNonDirectBounds
      block P hr hs hcomponent hbinary) :
    DegreeThreeFourBlockBinaryAxisEnvelope
      block P hr hs hcomponent hbinary where
  cellBound := C.selectedCellBound block P
  cellBound_nonneg := by
    intro b J D
    cases hchoice : degreeThreeFourBlockBinaryAxisChoice
        block P hr hs hcomponent hbinary D with
    | direct A =>
        simp only [selectedCellBound, hchoice]
        apply mul_nonneg (by positivity)
        exact (Nat.cast_nonneg _).trans
          (degreeThreeFourBlockBinary_directAxis_epi_le
            block P hr hs hcomponent D A J)
    | supported S =>
        simpa only [selectedCellBound, hchoice] using
          C.supported_nonneg D S b J
    | criticalE8 hE8 =>
        simpa only [selectedCellBound, hchoice] using
          C.critical_nonneg D hE8 b J
  direct := by
    intro D A hA b J
    simpa only [selectedCellBound, hA] using
      degreeThreeFourBlockBinary_directAxis_joint_le block P
        hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
        hr hs hcomponent D A J
  supported := by
    intro D S hS hchoice b J
    simpa only [selectedCellBound, hchoice] using
      C.supported_le D ⟨S, hS⟩ b J
  criticalE8 := by
    intro D hE8 hchoice b J
    simpa only [selectedCellBound, hchoice] using
      C.critical_le D hE8 b J

end DegreeThreeFourBlockBinaryNonDirectBounds

/-- Install a branchwise literal-axis envelope once its *single* summed
capacity estimate has been proved.  The aggregate hypothesis is downstream
of the direct/carrier/E8 split, so it cannot silently replace the correlated
cell bounds by a product of separate maxima. -/
noncomputable def DegreeThreeFourBlockBinaryJointBound.ofAxisEnvelope
    {hr : Nat.card block.Fibre = 3}
    {hs : Nat.card block.Points = 4}
    {hcomponent : Nat.card block.Component = 6}
    {hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action}
    (C : DegreeThreeFourBlockBinaryAxisEnvelope
      block P hr hs hcomponent hbinary)
    (R : Type) [Group R] [Finite R]
    (v : ℕ) (action : R →* Equiv.Perm (Fin v))
    (action_injective : Function.Injective action)
    (mainCoefficient : ℝ) (coldCoefficient : ℕ → ℝ)
    (eta theta : ℝ)
    (mainCoefficient_nonneg : 0 ≤ mainCoefficient)
    (coldCoefficient_nonneg : ∀ b, 0 ≤ coldCoefficient b)
    (exceptionalRaw : ℕ → ℝ)
    (exceptionalRaw_nonneg : ∀ b, 0 ≤ exceptionalRaw b)
    (aggregate : ∀ b : ℕ,
      (∑ J : Subgroup (Equiv.Perm (Fin b)),
        ∑ D : {D : Subgroup
            (preE7NonPairAction w U ⧸ E block P) // D.Normal},
          C.cellBound b J D) ≤
        ((∑ J : Subgroup (Equiv.Perm (Fin b)),
            ((mainCoefficient * (2 : ℝ) ^ (eta * b)) *
                completeQuotientWeight (R := R) J +
              coldCoefficient b * (2 : ℝ) ^ (theta * b))) +
          exceptionalRaw b)) :
    DegreeThreeFourBlockBinaryJointBound block P hr hs hcomponent hbinary where
  R := R
  groupR := inferInstance
  finiteR := inferInstance
  v := v
  action := action
  action_injective := action_injective
  mainCoefficient := mainCoefficient
  coldCoefficient := coldCoefficient
  eta := eta
  theta := theta
  mainCoefficient_nonneg := mainCoefficient_nonneg
  coldCoefficient_nonneg := coldCoefficient_nonneg
  exceptionalRaw := exceptionalRaw
  exceptionalRaw_nonneg := exceptionalRaw_nonneg
  summed := fun b ↦
    (DegreeThreeFourBlockBinaryAxisEnvelope.jointSum_le
      (block := block) (P := P) C b).trans (aggregate b)

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
