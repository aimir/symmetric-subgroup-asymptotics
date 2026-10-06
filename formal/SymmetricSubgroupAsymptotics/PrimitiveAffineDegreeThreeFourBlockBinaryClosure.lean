import SymmetricSubgroupAsymptotics.JointElementaryLayerExactTop
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockBinaryAxisCoverage
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockPartialAssembly
import SymmetricSubgroupAsymptotics.BinaryDegreeEightCarrierSourceBridge

/-!
# Exact joint boundary for the binary four-block signed quotient

The uniform ternary prepend cannot be multiplied by a separately estimated
degree-eight carrier row: at four blocks that loses the numerical margin.
This file instead regroups the literal affine elementary incidence over its
actual top normals.  On that same normal it records the checked degree-eight
alternative, either a direct original-weight owner or its exact carrier
slot.  Thus the remaining estimate is one joint sum; no worst-case product
of a ternary bound and a binary bound occurs in the interface.

Everything around that joint estimate is discharged here.  In particular,
the exact fixed-top regrouping is transported through the literal pair chart,
an arbitrary surviving source is bounded by the joint sum, and a proved
numerical estimate installs a final `PreE7RankTailSourceOrYonedaTopData`.
The sole remaining mathematical input is
`DegreeThreeFourBlockBinaryJointIncidenceTheorem` below.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

open BinaryDegreeEightPhysicalAnalyticClosure
open BinaryDegreeEightDirectEntryCoverage
open BinaryDegreeEightCarrierSourceBridge

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

/-- The exact translation chart has finite carrier because its multiplicative
coordinates embed back into the finite ambient kernel. -/
noncomputable instance degreeThreeFourBlockElementaryChart_finite :
    Finite (elementaryChart block P).V := by
  letI : Finite (chart block P).V := Finite.of_injective
    (fun v : (chart block P).V ↦
      (chart block P).equiv.symm (Multiplicative.ofAdd v))
    (chart block P).equiv.symm.injective
  change Finite (TranslationSubmodule block P)
  exact Finite.of_injective (TranslationSubmodule block P).subtype
    (TranslationSubmodule block P).subtype_injective

noncomputable instance degreeThreeFourBlockElementaryRepresentation_finite :
    Finite (elementaryChart block P).quotientRepresentation :=
  inferInstanceAs (Finite (elementaryChart block P).V)

/-! ## Literal top axes and their checked binary destination -/

/-- Transport one actual signed-quotient normal to the fixed eight-point
pair chart. -/
def degreeThreeFourBlockBinaryChartAxis
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (D : Subgroup (preE7NonPairAction w U ⧸ E block P)) :
    Subgroup (degreeThreeFourBlockPairChart block P hr hs hcomponent).action :=
  D.map (degreeThreeFourBlockPairChart block P hr hs hcomponent).sourceEquiv.toMonoidHom

/-- A normal-axis subtype already carries the instance required by the
quotient and degree-eight entry APIs. -/
instance degreeThreeFourBlockBinaryOriginalAxis_normal
    (D : {D : Subgroup (preE7NonPairAction w U ⧸ E block P) // D.Normal}) :
    D.1.Normal :=
  D.2

instance degreeThreeFourBlockBinaryChartAxis_normal
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (D : Subgroup (preE7NonPairAction w U ⧸ E block P)) [D.Normal] :
    (degreeThreeFourBlockBinaryChartAxis block P hr hs hcomponent D).Normal :=
  Subgroup.Normal.map inferInstance _
    (degreeThreeFourBlockPairChart block P hr hs hcomponent).sourceEquiv.surjective

/-- Explicit mapped-normal proof for a literal normal-axis subtype.  This is
used in dependent entry types so elaboration never has to rediscover the
subtype's bundled proof by typeclass search. -/
@[reducible] def degreeThreeFourBlockBinaryChartAxisNormal
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (D : {D : Subgroup (preE7NonPairAction w U ⧸ E block P) // D.Normal}) :
    (degreeThreeFourBlockBinaryChartAxis block P hr hs hcomponent D.1).Normal :=
  Subgroup.Normal.map D.2 _
    (degreeThreeFourBlockPairChart block P hr hs hcomponent).sourceEquiv.surjective

/-- The three counting-relevant outcomes on one literal binary top axis.
The direct branch retains its complete weighted entry.  A genuine carrier
branch retains positive noncritical support.  The only zero-support outcome
identifies the entire signed-quotient action with the regular critical E8
action, rather than merely recording an arbitrary all-E8 slot. -/
inductive DegreeThreeFourBlockBinaryAxisChoice
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (D : {D : Subgroup (preE7NonPairAction w U ⧸ E block P) // D.Normal}) : Type 2
  | direct : @DirectEntry8
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action
      (degreeThreeFourBlockBinaryChartAxis block P hr hs hcomponent D.1)
      (degreeThreeFourBlockBinaryChartAxisNormal block P hr hs hcomponent D) →
      DegreeThreeFourBlockBinaryAxisChoice hr hs hcomponent D
  | supported : {S : AxisSlot
        (degreeThreeFourBlockPairChart block P hr hs hcomponent).action
        (degreeThreeFourBlockBinaryChartAxis block P hr hs hcomponent D.1) //
      S.HasNoncritical} →
      DegreeThreeFourBlockBinaryAxisChoice hr hs hcomponent D
  | criticalE8 : IsE8Action
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action →
      DegreeThreeFourBlockBinaryAxisChoice hr hs hcomponent D

/-- Choose the checked destination on every literal top normal.  The choice
is made before the exterior degree and source subgroup are introduced. -/
noncomputable def degreeThreeFourBlockBinaryAxisChoice
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (D : {D : Subgroup (preE7NonPairAction w U ⧸ E block P) // D.Normal}) :
    DegreeThreeFourBlockBinaryAxisChoice block P hr hs hcomponent D := by
  letI : (degreeThreeFourBlockBinaryChartAxis block P hr hs hcomponent D.1).Normal :=
    degreeThreeFourBlockBinaryChartAxisNormal block P hr hs hcomponent D
  exact Classical.choice (show Nonempty
      (DegreeThreeFourBlockBinaryAxisChoice block P hr hs hcomponent D) from by
    rcases degreeThreeFourBlockBinary_axis_weighted_or_carrier block P hr hs
        hcomponent hbinary
        (degreeThreeFourBlockBinaryChartAxis block P hr hs hcomponent D.1) with
      hdirect | hcarrier
    · exact ⟨.direct (Classical.choice hdirect)⟩
    · rcases supportedAxisSlot_or_isE8Action hcarrier with hsupported | he8
      · exact ⟨.supported (Classical.choice hsupported)⟩
      · exact ⟨.criticalE8 he8⟩)

/-! ## The exact coupled incidence -/

/-- Quotient equivalence from the actual signed-quotient top axis to its
literal eight-point charted axis. -/
noncomputable def degreeThreeFourBlockBinaryAxisQuotientEquiv
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (D : {D : Subgroup (preE7NonPairAction w U ⧸ E block P) // D.Normal}) :
    ((preE7NonPairAction w U ⧸ E block P) ⧸ D.1) ≃*
      ((degreeThreeFourBlockPairChart block P hr hs hcomponent).action ⧸
        degreeThreeFourBlockBinaryChartAxis block P hr hs hcomponent D.1) :=
  QuotientGroup.congr D.1
    (degreeThreeFourBlockBinaryChartAxis block P hr hs hcomponent D.1)
    (degreeThreeFourBlockPairChart block P hr hs hcomponent).sourceEquiv rfl

theorem degreeThreeFourBlockBinary_topEpi_card_eq
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (D : {D : Subgroup (preE7NonPairAction w U ⧸ E block P) // D.Normal})
    {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))) :
    Nat.card (GroupEpimorphism J
        ((preE7NonPairAction w U ⧸ E block P) ⧸ D.1)) =
      Nat.card (GroupEpimorphism J
        ((degreeThreeFourBlockPairChart block P hr hs hcomponent).action ⧸
          degreeThreeFourBlockBinaryChartAxis block P hr hs hcomponent D.1)) :=
  fusionGroupEpimorphism_card_congr (MulEquiv.refl J)
    (degreeThreeFourBlockBinaryAxisQuotientEquiv block P hr hs hcomponent D)

/-- A retained direct entry bounds the top epimorphisms on this same literal
axis.  The survival predicate is unrestricted here because the terminal
predicate is imposed only after the ternary and binary factors have been
joined. -/
theorem degreeThreeFourBlockBinary_directAxis_epi_le
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (D : {D : Subgroup (preE7NonPairAction w U ⧸ E block P) // D.Normal})
    (A : @DirectEntry8
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action
      (degreeThreeFourBlockBinaryChartAxis block P hr hs hcomponent D.1)
      (degreeThreeFourBlockBinaryChartAxisNormal block P hr hs hcomponent D))
    {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))) :
    (Nat.card (GroupEpimorphism J
      ((degreeThreeFourBlockPairChart block P hr hs hcomponent).action ⧸
        degreeThreeFourBlockBinaryChartAxis block P hr hs hcomponent D.1)) : ℝ) ≤
      fusionLocalFactor b 4 A.prefixDegree A.liftConstant A.gapParameter *
        A.momentWeight J := by
  have h := A.original_envelope (fun _ ↦ True) J
  have hcard : Nat.card {beta : GroupEpimorphism J
      ((degreeThreeFourBlockPairChart block P hr hs hcomponent).action ⧸
        degreeThreeFourBlockBinaryChartAxis block P hr hs hcomponent D.1) //
      True} =
      Nat.card (GroupEpimorphism J
        ((degreeThreeFourBlockPairChart block P hr hs hcomponent).action ⧸
          degreeThreeFourBlockBinaryChartAxis block P hr hs hcomponent D.1)) := by
    simp
  unfold fusionSurvivingEpiCount at h
  rw [hcard] at h
  exact h

/-- One top-normal summand of the required coupled estimate.  The scalar
term is independent of how the axis is classified, while
`degreeThreeFourBlockBinaryAxisChoice` retains the direct entry, supported
carrier slot, or critical-E8 witness on this same literal normal for the
proof of the final estimate. -/
def degreeThreeFourBlockBinaryJointTopTerm
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (_hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (b : ℕ)
    (J : Subgroup (Equiv.Perm (Fin b)))
    (D : {D : Subgroup (preE7NonPairAction w U ⧸ E block P) // D.Normal}) :
    ℝ :=
  (Nat.card (GroupEpimorphism J
      ((degreeThreeFourBlockPairChart block P hr hs hcomponent).action ⧸
        degreeThreeFourBlockBinaryChartAxis block P hr hs hcomponent D.1)) : ℝ) *
    elementaryLayerExactTopContribution
      (elementaryChart block P).p (QuotientGroup.mk' (E block P))
      (QuotientGroup.mk'_surjective (E block P))
      (elementaryChart block P).quotientRepresentation
      (elementaryChart block P).originalKernelChart D b

theorem degreeThreeFourBlockBinaryJointTopTerm_eq
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (b : ℕ)
    (J : Subgroup (Equiv.Perm (Fin b)))
    (D : {D : Subgroup (preE7NonPairAction w U ⧸ E block P) // D.Normal}) :
    degreeThreeFourBlockBinaryJointTopTerm block P hr hs hcomponent hbinary b J D =
      (Nat.card (GroupEpimorphism J
        ((degreeThreeFourBlockPairChart block P hr hs hcomponent).action ⧸
          degreeThreeFourBlockBinaryChartAxis block P hr hs hcomponent D.1)) : ℝ) *
        elementaryLayerExactTopContribution
          (elementaryChart block P).p (QuotientGroup.mk' (E block P))
          (QuotientGroup.mk'_surjective (E block P))
          (elementaryChart block P).quotientRepresentation
          (elementaryChart block P).originalKernelChart D b :=
  rfl

/-- Uniform direct-axis budget.  This lemma is intentionally not applied to
carrier axes: there the factor on the left must stay coupled to the retained
slot.  It records all of the easy ternary numerics needed by the direct
branch of the missing theorem. -/
theorem degreeThreeFourBlockBinary_directTopContribution_le
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (D : {D : Subgroup (preE7NonPairAction w U ⧸ E block P) // D.Normal})
    (b : ℕ) :
    elementaryLayerExactTopContribution
        (elementaryChart block P).p (QuotientGroup.mk' (E block P))
        (QuotientGroup.mk'_surjective (E block P))
        (elementaryChart block P).quotientRepresentation
        (elementaryChart block P).originalKernelChart D b ≤
      (2 : ℝ) ^ (384 : ℝ) *
        (3 : ℝ) ^ ((b : ℝ) / 3) := by
  let H := translationLayerJointCapacity block P hTraceyHalf hTraceyLog
    hTraceyRefined hTraceyPerm
  have huniform := elementaryLayerExactTopContribution_le_uniform
    (elementaryChart block P).p (QuotientGroup.mk' (E block P))
    (QuotientGroup.mk'_surjective (E block P))
    (elementaryChart block P).quotientRepresentation
    (elementaryChart block P).originalKernelChart H D b
  have hp : (elementaryChart block P).p = 3 := by
    simpa only [elementaryChart, localTranslationChart] using
      (degreeThree_translation_prime_dim block P hr).1
  have hcap := degreeThree_translation_capacity_fourBlocks block P
    hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm hr hs
  have hcoeff := degreeThreeFourBlock_translationCoefficient_le_two_rpow
    block P hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm hr hs
  have hb : (0 : ℝ) ≤ (b : ℝ) / (elementaryChart block P).p := by
    positivity
  have hexp : H.capacity *
        ((b : ℝ) / (elementaryChart block P).p) ≤
      (b : ℝ) / (elementaryChart block P).p := by
    nlinarith
  have hpbase : (1 : ℝ) ≤ ((elementaryChart block P).p : ℝ) := by
    rw [hp]
    norm_num
  have hpow : ((elementaryChart block P).p : ℝ) ^
        (H.capacity * ((b : ℝ) / (elementaryChart block P).p)) ≤
      ((elementaryChart block P).p : ℝ) ^
        ((b : ℝ) / (elementaryChart block P).p) :=
    Real.rpow_le_rpow_of_exponent_le hpbase hexp
  calc
    _ ≤ H.coefficient * ((elementaryChart block P).p : ℝ) ^
          (H.capacity * ((b : ℝ) / (elementaryChart block P).p)) := huniform
    _ ≤ (2 : ℝ) ^ (384 : ℝ) *
          ((elementaryChart block P).p : ℝ) ^
            ((b : ℝ) / (elementaryChart block P).p) :=
      mul_le_mul hcoeff hpow (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        (by positivity)
    _ = (2 : ℝ) ^ (384 : ℝ) * (3 : ℝ) ^ ((b : ℝ) / 3) := by
      norm_num [hp]

/-- The direct branch is estimated as one literal-axis product: the same
normal supplies both the ternary exact-top contribution and the binary
original-weight entry.  This is the allowed direct specialization of the
joint incidence; carrier axes are deliberately excluded. -/
theorem degreeThreeFourBlockBinary_directAxis_joint_le
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (D : {D : Subgroup (preE7NonPairAction w U ⧸ E block P) // D.Normal})
    (A : @DirectEntry8
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action
      (degreeThreeFourBlockBinaryChartAxis block P hr hs hcomponent D.1)
      (degreeThreeFourBlockBinaryChartAxisNormal block P hr hs hcomponent D))
    {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))) :
    (Nat.card (GroupEpimorphism J
        ((degreeThreeFourBlockPairChart block P hr hs hcomponent).action ⧸
          degreeThreeFourBlockBinaryChartAxis block P hr hs hcomponent D.1)) : ℝ) *
      elementaryLayerExactTopContribution
        (elementaryChart block P).p (QuotientGroup.mk' (E block P))
        (QuotientGroup.mk'_surjective (E block P))
        (elementaryChart block P).quotientRepresentation
        (elementaryChart block P).originalKernelChart D b ≤
      ((2 : ℝ) ^ (384 : ℝ) * (3 : ℝ) ^ ((b : ℝ) / 3)) *
        (fusionLocalFactor b 4 A.prefixDegree A.liftConstant A.gapParameter *
          A.momentWeight J) := by
  have hepi := degreeThreeFourBlockBinary_directAxis_epi_le
    block P hr hs hcomponent D A J
  have hternary := degreeThreeFourBlockBinary_directTopContribution_le
    block P hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm hr hs D b
  have hcontribution := elementaryLayerExactTopContribution_nonneg
    (elementaryChart block P).p (QuotientGroup.mk' (E block P))
    (QuotientGroup.mk'_surjective (E block P))
    (elementaryChart block P).quotientRepresentation
    (elementaryChart block P).originalKernelChart D b
  have hbinary : 0 ≤
      fusionLocalFactor b 4 A.prefixDegree A.liftConstant A.gapParameter *
        A.momentWeight J :=
    (Nat.cast_nonneg _).trans hepi
  calc
    _ ≤ (fusionLocalFactor b 4 A.prefixDegree A.liftConstant A.gapParameter *
          A.momentWeight J) *
        ((2 : ℝ) ^ (384 : ℝ) * (3 : ℝ) ^ ((b : ℝ) / 3)) :=
      mul_le_mul hepi hternary hcontribution hbinary
    _ = _ := mul_comm _ _

/-- Summing one direct literal-axis product keeps the binary moment on the
same source and spends exactly its retained prefix degree. -/
theorem degreeThreeFourBlockBinary_directAxis_joint_sum_le
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (D : {D : Subgroup (preE7NonPairAction w U ⧸ E block P) // D.Normal})
    (A : @DirectEntry8
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action
      (degreeThreeFourBlockBinaryChartAxis block P hr hs hcomponent D.1)
      (degreeThreeFourBlockBinaryChartAxisNormal block P hr hs hcomponent D))
    (b : ℕ) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)),
      (Nat.card (GroupEpimorphism J
          ((degreeThreeFourBlockPairChart block P hr hs hcomponent).action ⧸
            degreeThreeFourBlockBinaryChartAxis block P hr hs hcomponent D.1)) : ℝ) *
        elementaryLayerExactTopContribution
          (elementaryChart block P).p (QuotientGroup.mk' (E block P))
          (QuotientGroup.mk'_surjective (E block P))
          (elementaryChart block P).quotientRepresentation
          (elementaryChart block P).originalKernelChart D b) ≤
      ((2 : ℝ) ^ (384 : ℝ) * (3 : ℝ) ^ ((b : ℝ) / 3)) *
        (fusionLocalFactor b 4 A.prefixDegree A.liftConstant A.gapParameter *
          (subgroupCount (b + A.prefixDegree) : ℝ)) := by
  let T : ℝ := (2 : ℝ) ^ (384 : ℝ) * (3 : ℝ) ^ ((b : ℝ) / 3)
  let F : ℝ := fusionLocalFactor b 4 A.prefixDegree A.liftConstant A.gapParameter
  calc
    _ ≤ ∑ J : Subgroup (Equiv.Perm (Fin b)),
        T * (F * A.momentWeight J) :=
      Finset.sum_le_sum (fun J _ ↦ by
        simpa only [T, F] using
          degreeThreeFourBlockBinary_directAxis_joint_le block P
            hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
            hr hs hcomponent D A J)
    _ = T * (F *
        ∑ J : Subgroup (Equiv.Perm (Fin b)), A.momentWeight J) := by
      rw [← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ T * (F * (subgroupCount (b + A.prefixDegree) : ℝ)) := by
      apply mul_le_mul_of_nonneg_left
      · apply mul_le_mul_of_nonneg_left
        · simpa only [pow_one, one_mul] using A.moment_le b 1
        · unfold F fusionLocalFactor
          exact mul_nonneg A.liftConstant_nonneg (Real.rpow_nonneg (by norm_num) _)
      · dsimp [T]
        positivity

/-- The actual complete quotient weight is bounded by the sum of exact
ternary incidences paired with their literal binary direct/carrier slots. -/
theorem degreeThreeFourBlockBinary_completeQuotientWeight_le_jointTop
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))) :
    completeQuotientWeight (R := preE7NonPairAction w U) J ≤
      ∑ D : {D : Subgroup
          (preE7NonPairAction w U ⧸ E block P) // D.Normal},
        degreeThreeFourBlockBinaryJointTopTerm block P hr hs hcomponent
          hbinary b J D := by
  let C₀ := P.elementaryChart block.component_preprimitive
  letI : Fact P.p.Prime := C₀.primeFact
  letI : AddCommGroup C₀.V := C₀.addCommGroup
  letI : Module (ZMod P.p) C₀.V := C₀.module
  letI : FiniteDimensional (ZMod P.p) C₀.V := C₀.finiteDimensional
  letI : Finite C₀.V := Finite.of_injective
    (fun v : C₀.V ↦ C₀.equiv.symm (Multiplicative.ofAdd v))
    C₀.equiv.symm.injective
  letI : Finite (TranslationSubmodule block P) :=
    Finite.of_injective (TranslationSubmodule block P).subtype
      (TranslationSubmodule block P).subtype_injective
  letI : Finite (elementaryChart block P).V := by
    change Finite (TranslationSubmodule block P)
    infer_instance
  letI : Finite (elementaryChart block P).quotientRepresentation :=
    inferInstanceAs (Finite (elementaryChart block P).V)
  have hregroup := completeQuotientWeight_le_exactTopContributions
    (elementaryChart block P).p (QuotientGroup.mk' (E block P))
    (QuotientGroup.mk'_surjective (E block P))
    (elementaryChart block P).quotientRepresentation
    (elementaryChart block P).originalKernelChart J
  refine hregroup.trans_eq ?_
  unfold degreeThreeFourBlockBinaryJointTopTerm
  simp_rw [degreeThreeFourBlockBinary_topEpi_card_eq
    block P hr hs hcomponent (J := J)]
  apply Finset.sum_congr
  · ext D
    simp
  · intro D hD
    rfl

/-! ## The one remaining joint theorem and its installation -/

/-- A numerical estimate of the literal coupled sum.  Its left side is
fixed above and retains, on every top normal, both the exact elementary
annihilator contribution and the checked direct/carrier payload. -/
structure DegreeThreeFourBlockBinaryJointBound
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action) : Type 1 where
  R : Type
  [groupR : Group R]
  [finiteR : Finite R]
  v : ℕ
  action : R →* Equiv.Perm (Fin v)
  action_injective : Function.Injective action
  mainCoefficient : ℝ
  coldCoefficient : ℕ → ℝ
  eta : ℝ
  theta : ℝ
  mainCoefficient_nonneg : 0 ≤ mainCoefficient
  coldCoefficient_nonneg : ∀ b, 0 ≤ coldCoefficient b
  exceptionalRaw : ℕ → ℝ
  exceptionalRaw_nonneg : ∀ b, 0 ≤ exceptionalRaw b
  summed : ∀ b : ℕ,
    (∑ J : Subgroup (Equiv.Perm (Fin b)),
      ∑ D : {D : Subgroup
          (preE7NonPairAction w U ⧸ E block P) // D.Normal},
        degreeThreeFourBlockBinaryJointTopTerm block P hr hs hcomponent
          hbinary b J D) ≤
      ((∑ J : Subgroup (Equiv.Perm (Fin b)),
          ((mainCoefficient * (2 : ℝ) ^ (eta * b)) *
              completeQuotientWeight (R := R) J +
            coldCoefficient b * (2 : ℝ) ^ (theta * b))) +
        exceptionalRaw b)

attribute [instance]
  DegreeThreeFourBlockBinaryJointBound.groupR
  DegreeThreeFourBlockBinaryJointBound.finiteR

/-- The coupled bound is already an ambient complete-source estimate; the
ternary layer must not be prepended a second time. -/
noncomputable def DegreeThreeFourBlockBinaryJointBound.toSummedSource
    {hr : Nat.card block.Fibre = 3}
    {hs : Nat.card block.Points = 4}
    {hcomponent : Nat.card block.Component = 6}
    {hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action}
    (D : DegreeThreeFourBlockBinaryJointBound block P hr hs hcomponent hbinary) :
    PreE7DegreeTwoPairSummedSource w U where
  R := D.R
  groupR := D.groupR
  finiteR := D.finiteR
  v := D.v
  action := D.action
  action_injective := D.action_injective
  mainCoefficient := D.mainCoefficient
  coldCoefficient := D.coldCoefficient
  eta := D.eta
  theta := D.theta
  mainCoefficient_nonneg := D.mainCoefficient_nonneg
  coldCoefficient_nonneg := D.coldCoefficient_nonneg
  exceptionalRaw := D.exceptionalRaw
  exceptionalRaw_nonneg := D.exceptionalRaw_nonneg
  summed := by
    intro b source
    calc
      (∑ J : Subgroup (Equiv.Perm (Fin b)),
          fusionCompleteSourceSum (preE7NonPairAction w U) source J) ≤
        ∑ J : Subgroup (Equiv.Perm (Fin b)),
          completeQuotientWeight (R := preE7NonPairAction w U) J := by
        apply Finset.sum_le_sum
        intro J _
        unfold fusionCompleteSourceSum completeQuotientWeight
          completeQuotientCount
        rw [Nat.cast_sum]
        exact Finset.sum_le_sum (fun N _ ↦
          fusionSurvivingEpiCount_le_groupEpimorphism_card
            (preE7NonPairAction w U) source N J)
      _ ≤ ∑ J : Subgroup (Equiv.Perm (Fin b)),
          ∑ N : {N : Subgroup
              (preE7NonPairAction w U ⧸ E block P) // N.Normal},
            degreeThreeFourBlockBinaryJointTopTerm block P hr hs hcomponent
              hbinary b J N :=
        Finset.sum_le_sum (fun J _ ↦
          degreeThreeFourBlockBinary_completeQuotientWeight_le_jointTop
            block P hr hs hcomponent hbinary J)
      _ ≤ _ := D.summed b

/-- A proved coupled incidence together with the ordinary numerical terminal
conditions needed by the existing rank-tail endpoint. -/
structure DegreeThreeFourBlockBinaryJointClosure
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action) : Type 1 where
  bound : DegreeThreeFourBlockBinaryJointBound block P hr hs hcomponent hbinary
  numerics : (DegreeThreeFourBlockBinaryJointBound.toSummedSource
    block P bound).AdditiveNumericalMargin

namespace DegreeThreeFourBlockBinaryJointClosure

/-- Final source on the unchanged ambient degree-twelve action. -/
noncomputable def source
    {hr : Nat.card block.Fibre = 3}
    {hs : Nat.card block.Points = 4}
    {hcomponent : Nat.card block.Component = 6}
    {hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action}
    (D : DegreeThreeFourBlockBinaryJointClosure block P hr hs hcomponent hbinary) :
    PreE7RankTailSourceOrYonedaTopData w U :=
  .inr (.inr ((DegreeThreeFourBlockBinaryJointBound.toSummedSource
    block P D.bound).toResidualChoiceAdditive D.numerics))

end DegreeThreeFourBlockBinaryJointClosure

/-- **Exact remaining theorem.**  For every literal binary four-block cell,
bound the jointly retained elementary/top incidence above.  The theorem may
use the direct owner or carrier slot stored by
`degreeThreeFourBlockBinaryAxisChoice`; it may not replace the two factors by
independent worst-case estimates. -/
abbrev DegreeThreeFourBlockBinaryJointIncidenceTheorem :=
  ∀ {w : ℕ} (U : PreE7NonPairActionClass w)
    (basePoint : Fin w)
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action),
    Nonempty (DegreeThreeFourBlockBinaryJointClosure
      block P hr hs hcomponent hbinary)

/-- Once the exact joint theorem is proved, it fills the binary four-block
construction boundary used by the degree-three residual assembly. -/
noncomputable def degreeThreeFourBlockBinaryResidualSource_of_jointIncidence
    (joint : DegreeThreeFourBlockBinaryJointIncidenceTheorem) :
    DegreeThreeFourBlockBinaryResidualSource := by
  intro w U _hw basePoint block P _hNT _hres hr hs hcomponent _hK hbinary
  exact DegreeThreeFourBlockBinaryJointClosure.source block P
    (Classical.choice (joint U basePoint block P hr hs hcomponent hbinary))

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
