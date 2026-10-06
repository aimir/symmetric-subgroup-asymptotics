import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockBinaryExactTerminalExceptional
import SymmetricSubgroupAsymptotics.RepeatedMarkerPositiveRecurrence

/-!
# Forward-row terminal interface for the binary four-block affine cell

The exact terminal count has two mathematically different pieces.  Direct
axes use the already proved growing-quotient row.  Positive carrier axes are
physical continuation terms, so they must enter the ordinary recurrence as
a strictly forward row rather than being declared an exponentially decaying
scalar.  Critical `E8` axes are removed only by an actual earlier owner.

This file separates those three routes without enlarging a positive fibre.
The positive callback is stated in the ambient degree and uses the existing
degree-indexed repeated-marker kernel.  The remaining construction theorem
is the reversible four-marker carrier encoding which supplies that callback.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

/-- A residual row whose last term is itself a proved forward recurrence.
The function `Y` is indexed by complement degree; `ambientY` puts it back at
the original physical degree. -/
structure PreE7NumericalRankTailForwardResidualChoice
    (w : ℕ) (U : PreE7NonPairActionClass w) where
  D : ℕ → ℝ
  T : ℕ → ℝ
  v : ℕ
  eta : ℝ
  delta : ℝ
  cutoff : ℝ
  alpha : ℝ
  theta : ℝ
  Y : ℕ → ℝ
  alpha_eq : alpha = eta + cutoff
  D_nonneg : ∀ b, 0 ≤ D b
  T_nonneg : ∀ b, 0 ≤ T b
  T_le_D : ∀ b, T b ≤ D b
  parameters : PreE7CharacterEntryParameters preE7CharacterRho w v eta
    delta cutoff alpha theta
  main_total_growth :
    (∀ b, D b ≤ (2 : ℝ) ^
      (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2)) ∨
    (∀ b, D b ≤ (2 : ℝ) ^
      (PrimitiveAffineImprimitiveBlockTransfer.affineComponentWidthCost w +
        8 * (w : ℝ) * Real.logb 2 (b + 1)))
  forward : OrdinaryFrontierClosure.ExponentialForwardEstimate
    (fun n ↦ if w ≤ n then Y (n - w) else 0)
  local_bound : ∀ b,
    (Nat.card (FusionOrbitFamily (preE7NonPairAction w U)
      (FusionAcceptedOrbitPredicate (preE7NonPairAction w U)
        (preE7NoPairNoC3CertifiedFirstOwnerPredicate
          preE7NoPairNoC3EarlierNumericalRankTailFamilyAction w
          (Fin.last preE7NoPairNoC3EarlierOwnerCount, U) b))) : ℝ) /
        exactBenchmark (b + w) ≤
      growingQuotientHotKernel (fun n ↦ (subgroupCount n : ℝ))
          b w v (D b)
          (Nat.card (Subgroup.normalizer
            (preE7NonPairAction w U : Set (Equiv.Perm (Fin w)))) : ℝ)
          eta delta cutoff +
        fusionWidthColdKernel b w (D b)
          (Nat.card (Subgroup.normalizer
            (preE7NonPairAction w U : Set (Equiv.Perm (Fin w)))) : ℝ)
          alpha * ordinarySubgroupRatio b +
        fusionWidthColdKernel b w (T b)
          (Nat.card (Subgroup.normalizer
            (preE7NonPairAction w U : Set (Equiv.Perm (Fin w)))) : ℝ)
          theta * ordinarySubgroupRatio b + Y b

namespace PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

/-- The part of one selected cell which already has a direct
growing-quotient row. -/
def degreeThreeFourBlockBinaryExactDirectCell
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
  | .direct _ => degreeThreeFourBlockBinaryExactTerminalCell
      block P hr hs hcomponent hbinary b J D
  | .positive _ | .criticalE8 _ => 0

/-- The exact accepted fibre on a positive route.  No independent carrier
or elementary maximum is inserted here. -/
def degreeThreeFourBlockBinaryExactPositiveCell
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
  | .positive _ => degreeThreeFourBlockBinaryAcceptedTopTerm block P
      (degreeThreeFourBlockBinaryTerminalPredicate (U := U) b) J D
  | .direct _ | .criticalE8 _ => 0

theorem degreeThreeFourBlockBinaryExactTerminalCell_eq_direct_add_positive
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b)))
    (D : {D : Subgroup
      (preE7NonPairAction w U ⧸ E block P) // D.Normal}) :
    degreeThreeFourBlockBinaryExactTerminalCell
        block P hr hs hcomponent hbinary b J D =
      degreeThreeFourBlockBinaryExactDirectCell
          block P hr hs hcomponent hbinary b J D +
        degreeThreeFourBlockBinaryExactPositiveCell
          block P hr hs hcomponent hbinary b J D := by
  cases hchoice : degreeThreeFourBlockBinaryCertifiedAxisChoice
      block P hr hs hcomponent hbinary D <;>
    simp [degreeThreeFourBlockBinaryExactTerminalCell,
      degreeThreeFourBlockBinaryExactDirectCell,
      degreeThreeFourBlockBinaryExactPositiveCell, hchoice]

def degreeThreeFourBlockBinaryExactDirectRaw
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (b : ℕ) : ℝ :=
  ∑ J : Subgroup (Equiv.Perm (Fin b)),
    ∑ D : {D : Subgroup
        (preE7NonPairAction w U ⧸ E block P) // D.Normal},
      degreeThreeFourBlockBinaryExactDirectCell
        block P hr hs hcomponent hbinary b J D

def degreeThreeFourBlockBinaryExactPositiveRaw
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (b : ℕ) : ℝ :=
  ∑ J : Subgroup (Equiv.Perm (Fin b)),
    ∑ D : {D : Subgroup
        (preE7NonPairAction w U ⧸ E block P) // D.Normal},
      degreeThreeFourBlockBinaryExactPositiveCell
        block P hr hs hcomponent hbinary b J D

theorem degreeThreeFourBlockBinaryExactTerminalRaw_eq_direct_add_positive
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (b : ℕ) :
    degreeThreeFourBlockBinaryExactTerminalRaw
        block P hr hs hcomponent hbinary b =
      degreeThreeFourBlockBinaryExactDirectRaw
          block P hr hs hcomponent hbinary b +
        degreeThreeFourBlockBinaryExactPositiveRaw
          block P hr hs hcomponent hbinary b := by
  unfold degreeThreeFourBlockBinaryExactTerminalRaw
    degreeThreeFourBlockBinaryExactDirectRaw
    degreeThreeFourBlockBinaryExactPositiveRaw
  simp_rw [degreeThreeFourBlockBinaryExactTerminalCell_eq_direct_add_positive]
  simp only [Finset.sum_add_distrib]

/-- The positive raw source after the single original pointing factor. -/
def degreeThreeFourBlockBinaryExactPositiveNormalized
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (b : ℕ) : ℝ :=
  growingQuotientNormalizedPointing b w
      (Nat.card (Subgroup.normalizer
        (preE7NonPairAction w U : Set (Equiv.Perm (Fin w)))) : ℝ) *
    degreeThreeFourBlockBinaryExactPositiveRaw
      block P hr hs hcomponent hbinary b

/-- Exact target of the reversible carrier theorem.  Its row is the already
checked degree-indexed repeated-marker row at the original physical degree
`b+w`. -/
abbrev DegreeThreeFourBlockBinaryPositiveForwardCallback
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action) :=
  ∀ b : ℕ,
    degreeThreeFourBlockBinaryExactPositiveNormalized
        block P hr hs hcomponent hbinary b ≤
      ∑ m ∈ Finset.range (b + w),
        MarkerDegreeForwardRow.kernel (b + w) m * ordinarySubgroupRatio m

/-- A pointwise positive callback is a complete ambient forward estimate.
The only numerical input is the existing repeated-marker row decay. -/
noncomputable def degreeThreeFourBlockBinaryPositiveForwardEstimate
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (callback : DegreeThreeFourBlockBinaryPositiveForwardCallback
      block P hr hs hcomponent hbinary) :
    OrdinaryFrontierClosure.ExponentialForwardEstimate
      (fun n ↦ if w ≤ n then
        degreeThreeFourBlockBinaryExactPositiveNormalized
          block P hr hs hcomponent hbinary (n - w) else 0) := by
  let N := Classical.choose
    (Filter.eventually_atTop.mp MarkerDegreeForwardRow.eventually_row_le)
  have hN := Classical.choose_spec
    (Filter.eventually_atTop.mp MarkerDegreeForwardRow.eventually_row_le)
  refine
    { scalar := fun _ ↦ 0
      kernel := MarkerDegreeForwardRow.kernel
      threshold := max w N
      rate := 1 / 20
      scalarConst := 1
      rowConst := (2 : ℝ) ^ (1 / 20 : ℝ)
      rate_pos := by norm_num
      scalarConst_pos := by norm_num
      rowConst_nonneg := Real.rpow_nonneg (by norm_num) _
      kernel_nonneg := fun n _hn m _hm ↦
        MarkerDegreeForwardRow.kernel_nonneg n m
      recurrence := ?_
      scalar_decay := by
        intro n _hn
        positivity
      row_decay := ?_ }
  · intro n hn
    have hwn : w ≤ n := le_trans (le_max_left _ _) hn
    have hdegree : n - w + w = n := Nat.sub_add_cancel hwn
    simp only [if_pos hwn, zero_add]
    simpa only [hdegree] using callback (n - w)
  · intro n hn
    have hexponent : -(n : ℝ) / 20 = -(1 / 20 : ℝ) * n := by
      ring
    simpa only [hexponent] using
      hN n (le_trans (le_max_right _ _) hn)

/-- Direct-row data plus the honest positive forward callback.  There is no
`ExponentialScalarBound` field for the positive carrier family. -/
structure DegreeThreeFourBlockBinaryExactTerminalForwardData
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
  alpha_eq : alpha = eta + cutoff
  D_nonneg : ∀ b, 0 ≤ D b
  T_nonneg : ∀ b, 0 ≤ T b
  T_le_D : ∀ b, T b ≤ D b
  parameters : PreE7CharacterEntryParameters preE7CharacterRho w v eta
    delta cutoff alpha theta
  total_growth : ∀ b,
    D b ≤ (2 : ℝ) ^
      (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2)
  directAggregate : ∀ b : ℕ,
    degreeThreeFourBlockBinaryExactDirectRaw
        block P hr hs hcomponent hbinary b ≤
      ∑ J : Subgroup (Equiv.Perm (Fin b)),
        ((D b * (2 : ℝ) ^ (eta * b)) *
            completeQuotientWeight (R := R) J +
          T b * (2 : ℝ) ^ (theta * b))
  positiveForward : DegreeThreeFourBlockBinaryPositiveForwardCallback
    block P hr hs hcomponent hbinary

attribute [instance]
  DegreeThreeFourBlockBinaryExactTerminalForwardData.groupR
  DegreeThreeFourBlockBinaryExactTerminalForwardData.finiteR

namespace DegreeThreeFourBlockBinaryExactTerminalForwardData

variable
  {hr : Nat.card block.Fibre = 3}
  {hs : Nat.card block.Points = 4}
  {hcomponent : Nat.card block.Component = 6}
  {hbinary : IsPGroup 2
    (degreeThreeFourBlockPairChart block P hr hs hcomponent).action}
  (A : DegreeThreeFourBlockBinaryExactTerminalForwardData
    block P hr hs hcomponent hbinary)

/-- The exact terminal family receives the direct growing-quotient row plus
the separately proved positive physical continuation row. -/
noncomputable def forwardResidualChoice
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput) :
    PreE7NumericalRankTailForwardResidualChoice w U where
  D := A.D
  T := A.T
  v := A.v
  eta := A.eta
  delta := A.delta
  cutoff := A.cutoff
  alpha := A.alpha
  theta := A.theta
  Y := degreeThreeFourBlockBinaryExactPositiveNormalized
    block P hr hs hcomponent hbinary
  alpha_eq := A.alpha_eq
  D_nonneg := A.D_nonneg
  T_nonneg := A.T_nonneg
  T_le_D := A.T_le_D
  parameters := A.parameters
  main_total_growth := .inl A.total_growth
  forward := degreeThreeFourBlockBinaryPositiveForwardEstimate
    block P hr hs hcomponent hbinary A.positiveForward
  local_bound := by
    intro b
    let source := degreeThreeFourBlockBinaryTerminalPredicate (U := U) b
    have hsum :
        (∑ J : Subgroup (Equiv.Perm (Fin b)),
          fusionCompleteSourceSum (preE7NonPairAction w U) source J) ≤
          (∑ J : Subgroup (Equiv.Perm (Fin b)),
            ((A.D b * (2 : ℝ) ^ (A.eta * b)) *
                completeQuotientWeight (R := A.R) J +
              A.T b * (2 : ℝ) ^ (A.theta * b))) +
            degreeThreeFourBlockBinaryExactPositiveRaw
              block P hr hs hcomponent hbinary b := by
      calc
        _ ≤ degreeThreeFourBlockBinaryExactTerminalRaw
            block P hr hs hcomponent hbinary b :=
          degreeThreeFourBlockBinaryTerminalSummed_le_exactTerminalRaw
            block P hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
            hr hs hcomponent hbinary A.criticalOwner b
        _ = degreeThreeFourBlockBinaryExactDirectRaw
              block P hr hs hcomponent hbinary b +
            degreeThreeFourBlockBinaryExactPositiveRaw
              block P hr hs hcomponent hbinary b :=
          degreeThreeFourBlockBinaryExactTerminalRaw_eq_direct_add_positive
            block P hr hs hcomponent hbinary b
        _ ≤ _ := by
          simpa only [add_comm] using
            add_le_add_right (A.directAggregate b)
              (degreeThreeFourBlockBinaryExactPositiveRaw
                block P hr hs hcomponent hbinary b)
    have h :=
      fusionPhysical_growingQuotient_additiveTail_summedExceptional_kernel_bound
        (preE7NonPairAction w U) source
        (preE7NoPairNoC3CertifiedFirstOwnerPredicate_natural _ w
          (Fin.last preE7NoPairNoC3EarlierOwnerCount, U) b)
        A.action A.action_injective (A.D b) (A.T b) A.eta A.theta
        A.delta A.cutoff
        (degreeThreeFourBlockBinaryExactPositiveRaw
          block P hr hs hcomponent hbinary b)
        (A.D_nonneg b) (by simpa only [source] using hsum)
    simpa only [source, A.alpha_eq,
      degreeThreeFourBlockBinaryExactPositiveNormalized,
      ordinarySubgroupRatio] using h

end DegreeThreeFourBlockBinaryExactTerminalForwardData

/-- Correct remaining theorem boundary for the binary four-block cell.  Its
positive field is a forward recurrence, not a scalar-decay assertion. -/
abbrev DegreeThreeFourBlockBinaryExactTerminalForwardTheorem :=
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
    Nonempty (DegreeThreeFourBlockBinaryExactTerminalForwardData
      block P hr hs hcomponent hbinary)

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
