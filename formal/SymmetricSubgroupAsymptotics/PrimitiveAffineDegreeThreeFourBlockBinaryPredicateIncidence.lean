import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockBinaryJointIncidence

/-!
# Predicate-preserving incidence for the binary four-block cell

The all-epimorphism exact-top sum is useful on a direct axis, but it cannot
close the two genuinely physical branches.  A critical `E8` axis is removed
only by the earlier-owner predicate, and a positive carrier has to retain the
actual accepted subgroup while it is transported to the positive binary or
`S3`-marked carrier family.

This file therefore stops one step earlier.  It regroups the *surviving*
complete source exactly by the literal signed-quotient top normal.  Direct
axes may then be enlarged to the already proved all-epimorphism joint term.
The supported and critical branches remain on the accepted top fibre.  In
particular, a proof that the critical fibre is empty is now meaningful; it
was not meaningful after the terminal predicate had been discarded.
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

variable {w b : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

/-- The exact accepted contribution over one literal signed-quotient top.
Unlike `degreeThreeFourBlockBinaryJointTopTerm`, this has not forgotten the
terminal predicate. -/
def degreeThreeFourBlockBinaryAcceptedTopTerm
    (source : Subgroup
      (preE7NonPairAction w U × Equiv.Perm (Fin b)) → Prop)
    (J : Subgroup (Equiv.Perm (Fin b)))
    (D : {D : Subgroup
      (preE7NonPairAction w U ⧸ E block P) // D.Normal}) : ℝ :=
  ∑ N : {N : {N : Subgroup (preE7NonPairAction w U) // N.Normal} //
      elementaryLayerTopAxis
        (QuotientGroup.mk' (E block P))
        (QuotientGroup.mk'_surjective (E block P)) N = D},
    fusionSurvivingEpiCount (preE7NonPairAction w U) source N.1 J

omit [Nontrivial block.Fibre] in
/-- Exact fibrewise regrouping of the surviving complete source.  No
survival predicate, character flag, or continuation datum is erased. -/
theorem degreeThreeFourBlockBinary_completeSourceSum_eq_acceptedTop
    (source : Subgroup
      (preE7NonPairAction w U × Equiv.Perm (Fin b)) → Prop)
    (J : Subgroup (Equiv.Perm (Fin b))) :
    fusionCompleteSourceSum (preE7NonPairAction w U) source J =
      ∑ D : {D : Subgroup
          (preE7NonPairAction w U ⧸ E block P) // D.Normal},
        degreeThreeFourBlockBinaryAcceptedTopTerm block P source J D := by
  unfold fusionCompleteSourceSum degreeThreeFourBlockBinaryAcceptedTopTerm
  symm
  let f := fun N :
      {N : Subgroup (preE7NonPairAction w U) // N.Normal} ↦
        fusionSurvivingEpiCount
          (preE7NonPairAction w U) source N J
  calc
    (∑ D : {D : Subgroup
        (preE7NonPairAction w U ⧸ E block P) // D.Normal},
      ∑ N : {N : {N : Subgroup
          (preE7NonPairAction w U) // N.Normal} //
          elementaryLayerTopAxis
            (QuotientGroup.mk' (E block P))
            (QuotientGroup.mk'_surjective (E block P)) N = D},
        f N.1) =
        Finset.sum (@Finset.univ
          {N : Subgroup (preE7NonPairAction w U) // N.Normal}
          originalNormalFintype) f :=
      Fintype.sum_fiberwise
        (elementaryLayerTopAxis
          (QuotientGroup.mk' (E block P))
          (QuotientGroup.mk'_surjective (E block P))) f
    _ = Finset.sum (@Finset.univ
          {N : Subgroup (preE7NonPairAction w U) // N.Normal}
          (Subtype.fintype Subgroup.Normal)) f := by
      exact @Fintype.sum_equiv
        {N : Subgroup (preE7NonPairAction w U) // N.Normal}
        {N : Subgroup (preE7NonPairAction w U) // N.Normal} ℝ
        originalNormalFintype (Subtype.fintype Subgroup.Normal)
        inferInstance (Equiv.refl _) _ _ (fun _ ↦ rfl)

/-- On a direct axis it is safe to forget survival.  The resulting bound is
exactly the previously proved all-epimorphism joint top term on the same
literal normal, rather than a product of two independently selected maxima. -/
theorem degreeThreeFourBlockBinaryAcceptedTopTerm_le_jointTopTerm
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (source : Subgroup
      (preE7NonPairAction w U × Equiv.Perm (Fin b)) → Prop)
    (J : Subgroup (Equiv.Perm (Fin b)))
    (D : {D : Subgroup
      (preE7NonPairAction w U ⧸ E block P) // D.Normal}) :
    degreeThreeFourBlockBinaryAcceptedTopTerm block P source J D ≤
      degreeThreeFourBlockBinaryJointTopTerm block P hr hs hcomponent
        hbinary b J D := by
  unfold degreeThreeFourBlockBinaryAcceptedTopTerm
  calc
    (∑ N : {N : {N : Subgroup (preE7NonPairAction w U) // N.Normal} //
        elementaryLayerTopAxis
          (QuotientGroup.mk' (E block P))
          (QuotientGroup.mk'_surjective (E block P)) N = D},
      fusionSurvivingEpiCount
        (preE7NonPairAction w U) source N.1 J) ≤
      ∑ N : {N : {N : Subgroup (preE7NonPairAction w U) // N.Normal} //
          elementaryLayerTopAxis
            (QuotientGroup.mk' (E block P))
            (QuotientGroup.mk'_surjective (E block P)) N = D},
        (Nat.card (GroupEpimorphism J
          (preE7NonPairAction w U ⧸ N.1.1)) : ℝ) := by
      apply Finset.sum_le_sum
      intro N _
      exact fusionSurvivingEpiCount_le_groupEpimorphism_card
        (preE7NonPairAction w U) source N.1 J
    _ ≤ ∑ N : {N : {N : Subgroup
          (preE7NonPairAction w U) // N.Normal} //
          elementaryLayerTopAxis
            (QuotientGroup.mk' (E block P))
            (QuotientGroup.mk'_surjective (E block P)) N = D},
        (Nat.card (GroupEpimorphism J
          ((preE7NonPairAction w U ⧸ E block P) ⧸
            (elementaryLayerTopAxis
              (QuotientGroup.mk' (E block P))
              (QuotientGroup.mk'_surjective (E block P)) N.1).1)) : ℝ) *
          elementaryLayerExactAxisFactor
            (elementaryChart block P).p
            (QuotientGroup.mk' (E block P))
            (elementaryChart block P).quotientRepresentation
            (elementaryChart block P).originalKernelChart N.1 b := by
      apply Finset.sum_le_sum
      intro N _
      exact elementaryLayer_axis_epi_le_exact_top_exactCapacity
        (elementaryChart block P).p
        (QuotientGroup.mk' (E block P))
        (QuotientGroup.mk'_surjective (E block P))
        (elementaryChart block P).quotientRepresentation
        (elementaryChart block P).originalKernelChart N.1 J
    _ = (Nat.card (GroupEpimorphism J
          ((preE7NonPairAction w U ⧸ E block P) ⧸ D.1)) : ℝ) *
        elementaryLayerExactTopContribution
          (elementaryChart block P).p
          (QuotientGroup.mk' (E block P))
          (QuotientGroup.mk'_surjective (E block P))
          (elementaryChart block P).quotientRepresentation
          (elementaryChart block P).originalKernelChart D b := by
      rw [elementaryLayerExactTopContribution, Finset.mul_sum]
      let Fibre := {N : {N : Subgroup
          (preE7NonPairAction w U) // N.Normal} //
          elementaryLayerTopAxis
            (QuotientGroup.mk' (E block P))
            (QuotientGroup.mk'_surjective (E block P)) N = D}
      let originalFibreFintype : Fintype Fibre := by
        letI : Fintype
            {N : Subgroup (preE7NonPairAction w U) // N.Normal} :=
          originalNormalFintype
        infer_instance
      let lhsSummand : Fibre → ℝ := fun N ↦
        (Nat.card (GroupEpimorphism J
          ((preE7NonPairAction w U ⧸ E block P) ⧸
            (elementaryLayerTopAxis
              (QuotientGroup.mk' (E block P))
              (QuotientGroup.mk'_surjective (E block P)) N.1).1)) : ℝ) *
          elementaryLayerExactAxisFactor
            (elementaryChart block P).p
            (QuotientGroup.mk' (E block P))
            (elementaryChart block P).quotientRepresentation
            (elementaryChart block P).originalKernelChart N.1 b
      let rhsSummand : Fibre → ℝ := fun N ↦
        (Nat.card (GroupEpimorphism J
          ((preE7NonPairAction w U ⧸ E block P) ⧸ D.1)) : ℝ) *
          elementaryLayerExactAxisFactor
            (elementaryChart block P).p
            (QuotientGroup.mk' (E block P))
            (elementaryChart block P).quotientRepresentation
            (elementaryChart block P).originalKernelChart N.1 b
      exact @Fintype.sum_equiv Fibre Fibre ℝ
        originalFibreFintype
        (@Subtype.fintype
          {N : Subgroup (preE7NonPairAction w U) // N.Normal}
          (fun N ↦ elementaryLayerTopAxis
            (QuotientGroup.mk' (E block P))
            (QuotientGroup.mk'_surjective (E block P)) N = D)
          (fun a ↦ (elementaryLayerTopAxis
            (QuotientGroup.mk' (E block P))
            (QuotientGroup.mk'_surjective (E block P)) a).instDecidableEq D)
          (Subtype.fintype Subgroup.Normal))
        inferInstance
        (Equiv.refl Fibre) lhsSummand rhsSummand (fun N ↦ by
          simp only [Equiv.refl_apply]
          dsimp only [lhsSummand, rhsSummand]
          rw [N.2])
    _ = degreeThreeFourBlockBinaryJointTopTerm block P hr hs hcomponent
          hbinary b J D := by
      unfold degreeThreeFourBlockBinaryJointTopTerm
      rw [degreeThreeFourBlockBinary_topEpi_card_eq
        block P hr hs hcomponent D J]

/-- The predicate-preserving direct branch, obtained by the single allowed
relaxation to the all-epimorphism joint term. -/
theorem degreeThreeFourBlockBinaryAcceptedTopTerm_direct_le
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (source : Subgroup
      (preE7NonPairAction w U × Equiv.Perm (Fin b)) → Prop)
    (D : {D : Subgroup
      (preE7NonPairAction w U ⧸ E block P) // D.Normal})
    (A : @DirectEntry8
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action
      (degreeThreeFourBlockBinaryChartAxis block P hr hs hcomponent D.1)
      (degreeThreeFourBlockBinaryChartAxisNormal block P hr hs hcomponent D))
    (J : Subgroup (Equiv.Perm (Fin b))) :
    degreeThreeFourBlockBinaryAcceptedTopTerm block P source J D ≤
      ((2 : ℝ) ^ (384 : ℝ) * (3 : ℝ) ^ ((b : ℝ) / 3)) *
        (fusionLocalFactor b 4 A.prefixDegree A.liftConstant A.gapParameter *
          A.momentWeight J) := by
  exact (degreeThreeFourBlockBinaryAcceptedTopTerm_le_jointTopTerm
    block P hr hs hcomponent hbinary source J D).trans
      (degreeThreeFourBlockBinary_directAxis_joint_le block P
        hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
        hr hs hcomponent D A J)

/-- The two physical obligations left after the direct branch has been
removed.  `supportedValue` is the actual positive binary/S3 carrier count.
The critical statement is an equality to zero on the retained terminal
predicate, rather than an invalid all-epimorphism assertion. -/
structure DegreeThreeFourBlockBinaryPredicateNonDirectBounds
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (source : Subgroup
      (preE7NonPairAction w U × Equiv.Perm (Fin b)) → Prop) : Type 2 where
  supportedValue :
    (D : {D : Subgroup
      (preE7NonPairAction w U ⧸ E block P) // D.Normal}) →
    {S : AxisSlot
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action
      (degreeThreeFourBlockBinaryChartAxis block P hr hs hcomponent D.1) //
      S.HasNoncritical} →
    Subgroup (Equiv.Perm (Fin b)) → ℝ
  supported_nonneg : ∀ D S J, 0 ≤ supportedValue D S J
  supported_le : ∀ D S J,
    degreeThreeFourBlockBinaryAcceptedTopTerm block P source J D ≤
      supportedValue D S J
  critical_vanish : ∀
    (D : {D : Subgroup
      (preE7NonPairAction w U ⧸ E block P) // D.Normal})
    (_hE8 : IsE8Action
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (J : Subgroup (Equiv.Perm (Fin b))),
    degreeThreeFourBlockBinaryAcceptedTopTerm block P source J D = 0

namespace DegreeThreeFourBlockBinaryPredicateNonDirectBounds

/-- The selected accepted-cell cost.  The critical owner contributes
literally zero; no all-source count is substituted for it. -/
def selectedCellBound
    {hr : Nat.card block.Fibre = 3}
    {hs : Nat.card block.Points = 4}
    {hcomponent : Nat.card block.Component = 6}
    {hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action}
    {source : Subgroup
      (preE7NonPairAction w U × Equiv.Perm (Fin b)) → Prop}
    (C : DegreeThreeFourBlockBinaryPredicateNonDirectBounds
      block P hr hs hcomponent hbinary source)
    (J : Subgroup (Equiv.Perm (Fin b)))
    (D : {D : Subgroup
      (preE7NonPairAction w U ⧸ E block P) // D.Normal}) : ℝ :=
  match degreeThreeFourBlockBinaryAxisChoice
      block P hr hs hcomponent hbinary D with
  | .direct A =>
      ((2 : ℝ) ^ (384 : ℝ) * (3 : ℝ) ^ ((b : ℝ) / 3)) *
        (fusionLocalFactor b 4 A.prefixDegree A.liftConstant A.gapParameter *
          A.momentWeight J)
  | .supported S => C.supportedValue D S J
  | .criticalE8 _ => 0

theorem acceptedTopTerm_le_selectedCellBound
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    {hr : Nat.card block.Fibre = 3}
    {hs : Nat.card block.Points = 4}
    {hcomponent : Nat.card block.Component = 6}
    {hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action}
    {source : Subgroup
      (preE7NonPairAction w U × Equiv.Perm (Fin b)) → Prop}
    (C : DegreeThreeFourBlockBinaryPredicateNonDirectBounds
      block P hr hs hcomponent hbinary source)
    (J : Subgroup (Equiv.Perm (Fin b)))
    (D : {D : Subgroup
      (preE7NonPairAction w U ⧸ E block P) // D.Normal}) :
    degreeThreeFourBlockBinaryAcceptedTopTerm block P source J D ≤
      C.selectedCellBound block P J D := by
  cases hchoice : degreeThreeFourBlockBinaryAxisChoice
      block P hr hs hcomponent hbinary D with
  | direct A =>
      simpa only [selectedCellBound, hchoice] using
        degreeThreeFourBlockBinaryAcceptedTopTerm_direct_le block P
          hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
          hr hs hcomponent hbinary source D A J
  | supported S =>
      simpa only [selectedCellBound, hchoice] using C.supported_le D S J
  | criticalE8 hE8 =>
      rw [C.critical_vanish D hE8 J]
      simp only [selectedCellBound, hchoice]
      exact le_rfl

/-- Whole-source predicate-preserving aggregation.  This is the correct
entry point for the final positive-carrier numerical theorem. -/
theorem completeSourceSum_le_selectedCells
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    {hr : Nat.card block.Fibre = 3}
    {hs : Nat.card block.Points = 4}
    {hcomponent : Nat.card block.Component = 6}
    {hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action}
    {source : Subgroup
      (preE7NonPairAction w U × Equiv.Perm (Fin b)) → Prop}
    (C : DegreeThreeFourBlockBinaryPredicateNonDirectBounds
      block P hr hs hcomponent hbinary source)
    (J : Subgroup (Equiv.Perm (Fin b))) :
    fusionCompleteSourceSum (preE7NonPairAction w U) source J ≤
      ∑ D : {D : Subgroup
          (preE7NonPairAction w U ⧸ E block P) // D.Normal},
        C.selectedCellBound block P J D := by
  rw [degreeThreeFourBlockBinary_completeSourceSum_eq_acceptedTop block P]
  exact Finset.sum_le_sum (fun D _ ↦
    C.acceptedTopTerm_le_selectedCellBound block P
      hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm J D)

end DegreeThreeFourBlockBinaryPredicateNonDirectBounds

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
