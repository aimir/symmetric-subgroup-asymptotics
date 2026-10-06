import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockBinarySupportedIncidence
import SymmetricSubgroupAsymptotics.Non2PreE7RankTailSourceDichotomyClosure

/-!
# Terminal aggregation for the binary four-block affine cell

The exact-top files deliberately retain the terminal first-owner predicate.
This file packages the resulting last numerical step without widening that
predicate back to all epimorphisms.

For each literal signed-quotient top normal the checked degree-eight routing
has three outcomes.  A direct outcome uses its original-weight row.  A
positive outcome keeps the selected carrier quotient moment multiplied by
the elementary contribution on the same top.  A critical `E8` outcome is
zero only after an actual earlier owner of the ambient degree-twelve action
has been supplied.  The single aggregate inequality below is therefore the
remaining joint carrier-capacity theorem; it cannot be inhabited by separate
maxima for the ternary and binary factors.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

open BinaryCarrierS16TaggedPositiveRoutes
open BinaryDegreeEightCarrierSourceBridge

variable {w b : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

/-- The actual terminal predicate used by the final rank-tail catalogue. -/
abbrev degreeThreeFourBlockBinaryTerminalPredicate (b : ℕ) :
    Subgroup
      (preE7NonPairAction w U × Equiv.Perm (Fin b)) → Prop :=
  preE7NoPairNoC3CertifiedFirstOwnerPredicate
    preE7NoPairNoC3EarlierNumericalRankTailFamilyAction w
    (Fin.last preE7NoPairNoC3EarlierOwnerCount, U) b

/- An actual earlier owner of the ambient action makes every terminal
accepted top fibre empty.  The `E8` witness will be used only to construct
this owner; once the owner is present, no property of the witness is needed
for the zero statement. -/
omit [Nontrivial block.Fibre] in
lemma degreeThreeFourBlockBinaryAcceptedTopTerm_eq_zero_of_actionOwner
    (owner : PreE7NumericalRankTailActionOwner w U)
    (J : Subgroup (Equiv.Perm (Fin b)))
    (D : {D : Subgroup
      (preE7NonPairAction w U ⧸ E block P) // D.Normal}) :
    degreeThreeFourBlockBinaryAcceptedTopTerm block P
        (degreeThreeFourBlockBinaryTerminalPredicate (U := U) b) J D = 0 := by
  unfold degreeThreeFourBlockBinaryAcceptedTopTerm
  apply Finset.sum_eq_zero
  intro N _hN
  apply fusionSurvivingEpiCount_eq_zero_of_rejected
  intro beta hterminal
  letI : IsEmpty {H : Subgroup
      (preE7NonPairAction w U × Equiv.Perm (Fin b)) //
    FusionAcceptedOrbitPredicate (preE7NonPairAction w U)
      (degreeThreeFourBlockBinaryTerminalPredicate (U := U) b) H} :=
    preE7NumericalRankTail_terminalAccepted_isEmpty_of_actionOwner
      U owner b
  exact isEmptyElim
    (α := {H : Subgroup
        (preE7NonPairAction w U × Equiv.Perm (Fin b)) //
      FusionAcceptedOrbitPredicate (preE7NonPairAction w U)
        (degreeThreeFourBlockBinaryTerminalPredicate (U := U) b) H})
    (⟨(fusionFullGoursatEncode N.1 J beta).1,
      ⟨(fusionFullGoursatEncode N.1 J beta).2, hterminal⟩⟩ :
      {H : Subgroup
          (preE7NonPairAction w U × Equiv.Perm (Fin b)) //
        FusionAcceptedOrbitPredicate (preE7NonPairAction w U)
          (degreeThreeFourBlockBinaryTerminalPredicate (U := U) b) H})

/-- The route-selected cost on one literal top.  The positive branch keeps
the carrier chosen on this very top together with its exact elementary
factor; the critical branch is literally zero. -/
def degreeThreeFourBlockBinaryTerminalCellBound
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
  | .positive R =>
      completeQuotientWeight
          (R := (@BinaryCarrierS16TaggedPositiveRoutes.DegreeEightRoute.certified _ _
            (degreeThreeFourBlockBinaryChartAxisNormal
              block P hr hs hcomponent D) R).axisSlot.slot.carrier) J *
        elementaryLayerExactTopContribution
          (elementaryChart block P).p
          (QuotientGroup.mk' (E block P))
          (QuotientGroup.mk'_surjective (E block P))
          (elementaryChart block P).quotientRepresentation
          (elementaryChart block P).originalKernelChart D b
  | .criticalE8 _ => 0

theorem degreeThreeFourBlockBinaryTerminalCellBound_nonneg
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b)))
    (D : {D : Subgroup
      (preE7NonPairAction w U ⧸ E block P) // D.Normal}) :
    0 ≤ degreeThreeFourBlockBinaryTerminalCellBound
      block P hr hs hcomponent hbinary b J D := by
  cases hchoice : degreeThreeFourBlockBinaryCertifiedAxisChoice
      block P hr hs hcomponent hbinary D with
  | direct A =>
      simp only [degreeThreeFourBlockBinaryTerminalCellBound, hchoice]
      apply mul_nonneg
        (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
          (Real.rpow_nonneg (by norm_num) _))
      exact (Nat.cast_nonneg _).trans
        (degreeThreeFourBlockBinary_directAxis_epi_le
          block P hr hs hcomponent D A J)
  | positive R =>
      simp only [degreeThreeFourBlockBinaryTerminalCellBound, hchoice]
      exact mul_nonneg (completeQuotientWeight_nonneg J)
        (elementaryLayerExactTopContribution_nonneg
          (elementaryChart block P).p
          (QuotientGroup.mk' (E block P))
          (QuotientGroup.mk'_surjective (E block P))
          (elementaryChart block P).quotientRepresentation
          (elementaryChart block P).originalKernelChart D b)
  | criticalE8 hE8 =>
      simp only [degreeThreeFourBlockBinaryTerminalCellBound, hchoice]
      exact le_rfl

/-- One coherent source of the zero-motion implication: every critical
`E8` route must put the *ambient* action into an existing owner family. -/
abbrev DegreeThreeFourBlockBinaryCriticalOwnerData
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (_hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action) :=
  ∀ (_D : {D : Subgroup
      (preE7NonPairAction w U ⧸ E block P) // D.Normal}),
    IsE8Action
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action →
    PreE7NumericalRankTailActionOwner w U

/-- Every accepted terminal top is bounded by the route-selected cost.  The
positive route uses the exact carrier incidence already proved, while the
critical route is killed by its actual earlier owner. -/
theorem degreeThreeFourBlockBinaryAcceptedTopTerm_le_terminalCellBound
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
      degreeThreeFourBlockBinaryTerminalCellBound
        block P hr hs hcomponent hbinary b J D := by
  cases hchoice : degreeThreeFourBlockBinaryCertifiedAxisChoice
      block P hr hs hcomponent hbinary D with
  | direct A =>
      simpa only [degreeThreeFourBlockBinaryTerminalCellBound, hchoice] using
        degreeThreeFourBlockBinaryAcceptedTopTerm_direct_le block P
          hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
          hr hs hcomponent hbinary
          (degreeThreeFourBlockBinaryTerminalPredicate (U := U) b) D A J
  | positive R =>
      simpa only [degreeThreeFourBlockBinaryTerminalCellBound, hchoice] using
        degreeThreeFourBlockBinaryAcceptedTopTerm_positiveRoute_le block P
          hr hs hcomponent hbinary
          (degreeThreeFourBlockBinaryTerminalPredicate (U := U) b) J D R
  | criticalE8 hE8 =>
      rw [degreeThreeFourBlockBinaryAcceptedTopTerm_eq_zero_of_actionOwner
        block P (criticalOwner D hE8) J D]
      simp only [degreeThreeFourBlockBinaryTerminalCellBound, hchoice]
      exact le_rfl

/-- The exact terminal complete source is at most the sum of the correlated
route-selected cells. -/
theorem degreeThreeFourBlockBinaryTerminalCompleteSourceSum_le
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
    (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b))) :
    fusionCompleteSourceSum (preE7NonPairAction w U)
        (degreeThreeFourBlockBinaryTerminalPredicate (U := U) b) J ≤
      ∑ D : {D : Subgroup
          (preE7NonPairAction w U ⧸ E block P) // D.Normal},
        degreeThreeFourBlockBinaryTerminalCellBound
          block P hr hs hcomponent hbinary b J D := by
  rw [degreeThreeFourBlockBinary_completeSourceSum_eq_acceptedTop block P]
  exact Finset.sum_le_sum (fun D _ ↦
    degreeThreeFourBlockBinaryAcceptedTopTerm_le_terminalCellBound
      block P hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
      hr hs hcomponent hbinary criticalOwner b J D)

/-! ## The single remaining aggregate and its terminal installation -/

/-- Numerical data for the final correlated carrier sum.  `aggregate` is
the one place where all literal axes and complete sources are summed.  Its
left side contains the direct original-weight entries and the exact positive
carrier/elementary pairs selected above; no independent ternary or carrier
maximum occurs in this interface. -/
structure DegreeThreeFourBlockBinaryTerminalAggregate
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action) : Type 2 where
  criticalOwner : DegreeThreeFourBlockBinaryCriticalOwnerData
    block P hr hs hcomponent hbinary
  R : Type
  [groupR : Group R]
  [finiteR : Finite R]
  v : ℕ
  action : R →* Equiv.Perm (Fin v)
  action_injective : Function.Injective action
  D : ℕ → ℝ
  T : ℕ → ℝ
  eta : ℝ
  theta : ℝ
  delta : ℝ
  cutoff : ℝ
  alpha : ℝ
  rawExceptional : ℕ → ℝ
  alpha_eq : alpha = eta + cutoff
  D_nonneg : ∀ b, 0 ≤ D b
  T_nonneg : ∀ b, 0 ≤ T b
  T_le_D : ∀ b, T b ≤ D b
  rawExceptional_nonneg : ∀ b, 0 ≤ rawExceptional b
  width_upper : w ≤ 12288
  parameters : PreE7CharacterEntryParameters preE7CharacterRho w v eta
    delta cutoff alpha theta
  total_growth : ∀ b,
    D b ≤ (2 : ℝ) ^
      (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2)
  aggregate : ∀ b : ℕ,
    (∑ J : Subgroup (Equiv.Perm (Fin b)),
      ∑ D₀ : {D₀ : Subgroup
          (preE7NonPairAction w U ⧸ E block P) // D₀.Normal},
        degreeThreeFourBlockBinaryTerminalCellBound
          block P hr hs hcomponent hbinary b J D₀) ≤
      Finset.sum Finset.univ
          (fun J : Subgroup (Equiv.Perm (Fin b)) ↦
            (D b * (2 : ℝ) ^ (eta * b)) *
                completeQuotientWeight (R := R) J +
              T b * (2 : ℝ) ^ (theta * b)) +
        rawExceptional b
  exceptional : FusionCoarseEstimate (fun n ↦ (subgroupCount n : ℝ)) →
    ExponentialScalarBound (fun b ↦
      growingQuotientNormalizedPointing b w
          (Nat.card (Subgroup.normalizer
            (preE7NonPairAction w U : Set (Equiv.Perm (Fin w)))) : ℝ) *
        rawExceptional b)

attribute [instance]
  DegreeThreeFourBlockBinaryTerminalAggregate.groupR
  DegreeThreeFourBlockBinaryTerminalAggregate.finiteR

namespace DegreeThreeFourBlockBinaryTerminalAggregate

variable
  {hr : Nat.card block.Fibre = 3}
  {hs : Nat.card block.Points = 4}
  {hcomponent : Nat.card block.Component = 6}
  {hbinary : IsPGroup 2
    (degreeThreeFourBlockPairChart block P hr hs hcomponent).action}
  (A : DegreeThreeFourBlockBinaryTerminalAggregate
    block P hr hs hcomponent hbinary)

def normalizedExceptional (b : ℕ) : ℝ :=
  growingQuotientNormalizedPointing b w
      (Nat.card (Subgroup.normalizer
        (preE7NonPairAction w U : Set (Equiv.Perm (Fin w)))) : ℝ) *
    A.rawExceptional b

/-- The aggregate controls exactly the terminal source used downstream. -/
theorem terminalSummed
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (b : ℕ) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)),
      fusionCompleteSourceSum (preE7NonPairAction w U)
        (degreeThreeFourBlockBinaryTerminalPredicate (U := U) b) J) ≤
      Finset.sum Finset.univ
          (fun J : Subgroup (Equiv.Perm (Fin b)) ↦
            (A.D b * (2 : ℝ) ^ (A.eta * b)) *
                completeQuotientWeight (R := A.R) J +
              A.T b * (2 : ℝ) ^ (A.theta * b)) +
        A.rawExceptional b := by
  exact (Finset.sum_le_sum (fun J _ ↦
    degreeThreeFourBlockBinaryTerminalCompleteSourceSum_le
      block P hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
      hr hs hcomponent hbinary A.criticalOwner b J)).trans (A.aggregate b)

/-- Install the terminal-only aggregate directly in the final numerical
catalogue.  This avoids the stronger and false requirement that the same
bound hold for every arbitrary source predicate. -/
noncomputable def residualChoice
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput) :
    PreE7NumericalRankTailResidualChoice w U where
  D := A.D
  T := A.T
  v := A.v
  eta := A.eta
  delta := A.delta
  cutoff := A.cutoff
  alpha := A.alpha
  theta := A.theta
  X := A.normalizedExceptional block P
  alpha_eq := A.alpha_eq
  D_nonneg := A.D_nonneg
  T_nonneg := A.T_nonneg
  T_le_D := A.T_le_D
  parameters := A.parameters
  main_total_growth := .inl A.total_growth
  exceptional := A.exceptional
  exceptional_support := Or.inr A.width_upper
  local_bound := by
    intro b
    let source := degreeThreeFourBlockBinaryTerminalPredicate (U := U) b
    have h :=
      fusionPhysical_growingQuotient_additiveTail_summedExceptional_kernel_bound
        (preE7NonPairAction w U) source
        (preE7NoPairNoC3CertifiedFirstOwnerPredicate_natural _ w
          (Fin.last preE7NoPairNoC3EarlierOwnerCount, U) b)
        A.action A.action_injective (A.D b) (A.T b) A.eta A.theta
        A.delta A.cutoff (A.rawExceptional b) (A.D_nonneg b)
        (by
          simpa only [source] using
            (A.terminalSummed block P hTraceyHalf hTraceyLog
              hTraceyRefined hTraceyPerm b))
    simpa only [source, A.alpha_eq, normalizedExceptional,
      ordinarySubgroupRatio] using h

/-- Final construction-facing source for this one binary four-block cell. -/
noncomputable def source
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput) :
    PreE7RankTailSourceOrYonedaTopData w U :=
  .inr (.inr (A.residualChoice block P hTraceyHalf hTraceyLog
    hTraceyRefined hTraceyPerm))

end DegreeThreeFourBlockBinaryTerminalAggregate

/-- Exact remaining construction theorem after the local incidence and all
terminal plumbing have been discharged.  It must prove the critical-owner
implication and the one jointly summed direct/positive-carrier inequality. -/
abbrev DegreeThreeFourBlockBinaryTerminalCapacityTheorem :=
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
    Nonempty (DegreeThreeFourBlockBinaryTerminalAggregate
      block P hr hs hcomponent hbinary)

/-- The terminal capacity theorem fills the binary four-block construction
boundary without passing through the obsolete all-source joint bound. -/
noncomputable def degreeThreeFourBlockBinaryResidualSource_of_terminalCapacity
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (capacity : DegreeThreeFourBlockBinaryTerminalCapacityTheorem) :
    DegreeThreeFourBlockBinaryResidualSource := by
  intro w U _hw basePoint block P _hNT _hres hr hs hcomponent hK hbinary
  exact DegreeThreeFourBlockBinaryTerminalAggregate.source block P
    (Classical.choice
      (capacity U basePoint block P hr hs hcomponent hK hbinary))
    hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
