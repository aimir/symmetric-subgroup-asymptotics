import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockDistinctSignSource

/-!
# The two-sign four-block complete source

The two-sign proof has one bottom cyclic-dual term, the signed quotient
term, and finitely many proper two-dimensional translation-section terms.
This file keeps that decomposition correlated until every non-bottom term
has reached the same faithful degree-ten comparator.  It then performs the
single finite sum and checks the degree-twelve numerical windows.

The structure below is intentionally finer than `PreE7S3TwoSource`: it
retains the literal proper translation sections and the three inequalities
which produce the complete all-normal estimate.  No independent maximum of
the bottom and section terms is introduced.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

private abbrev NormalAxis (G : Type*) [Group G] :=
  {N : Subgroup G // N.Normal}

/-- Complete quotient weight of one bundled literal normal section. -/
noncomputable def bundledNormalQuotientWeight
    {G : Type*} [Group G] [Finite G]
    (N : NormalAxis G) {b : ℕ}
    (J : Subgroup (Equiv.Perm (Fin b))) : ℝ := by
  letI : N.1.Normal := N.2
  exact completeQuotientWeight (R := G ⧸ N.1) J

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

/-- The exact finite decomposition used by the two-sign proof.

`Section` indexes only the actual proper nonzero intersections with the
ternary translation layer.  `stratified_bound` is the normal-lattice
partition: bottom, axes containing the full translation layer, and the
listed proper sections.  The remaining fields compare all non-bottom terms
with one degree-ten action before their coefficients are added. -/
structure DegreeThreeFourBlockTwoSignComparison : Type 2 where
  Section : Type
  [fintypeSection : Fintype Section]
  sectionAxis : Section → NormalAxis (preE7NonPairAction w U)
  Q : Subgroup (Equiv.Perm (Fin 10))
  topCoefficient : ℝ
  sectionCoefficient : Section → ℝ
  tailCoefficient : ℝ
  topCoefficient_nonneg : 0 ≤ topCoefficient
  sectionCoefficient_nonneg : ∀ i, 0 ≤ sectionCoefficient i
  tailCoefficient_nonneg : 0 ≤ tailCoefficient
  stratified_bound : ∀ {b : ℕ}
      (J : Subgroup (Equiv.Perm (Fin b))),
    completeQuotientWeight (R := preE7NonPairAction w U) J ≤
      (Nat.card (GroupEpimorphism J (preE7NonPairAction w U)) : ℝ) +
        completeQuotientWeight
          (R := preE7NonPairAction w U ⧸ E block P) J +
        ∑ i : Section, bundledNormalQuotientWeight (sectionAxis i) J
  top_bound : ∀ {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))),
    completeQuotientWeight
        (R := preE7NonPairAction w U ⧸ E block P) J ≤
      topCoefficient * completeQuotientWeight (R := Q) J
  section_bound : ∀ (i : Section) {b : ℕ}
      (J : Subgroup (Equiv.Perm (Fin b))),
    bundledNormalQuotientWeight (sectionAxis i) J ≤
      sectionCoefficient i * completeQuotientWeight (R := Q) J
  tail_bound : ∀ {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))),
    (Nat.card (GroupEpimorphism J (preE7NonPairAction w U)) : ℝ) ≤
      tailCoefficient *
        (2 : ℝ) ^ ((Real.logb 2 3 / 3) * b)
  mainCoefficient_le :
    topCoefficient + ∑ i : Section, sectionCoefficient i ≤
      (2 : ℝ) ^ (384 : ℝ)
  tailCoefficient_le : tailCoefficient ≤ (2 : ℝ) ^ (384 : ℝ)

attribute [instance]
  DegreeThreeFourBlockTwoSignComparison.fintypeSection

namespace DegreeThreeFourBlockTwoSignComparison

variable (D : DegreeThreeFourBlockTwoSignComparison block P)

/-- The one combined comparator coefficient, after the actual section list
has been summed. -/
noncomputable def mainCoefficient : ℝ :=
  D.topCoefficient + ∑ i : D.Section, D.sectionCoefficient i

omit [Nontrivial block.Fibre] in
theorem mainCoefficient_nonneg : 0 ≤ D.mainCoefficient := by
  apply add_nonneg D.topCoefficient_nonneg
  exact Finset.sum_nonneg (fun i _ ↦ D.sectionCoefficient_nonneg i)

omit [Nontrivial block.Fibre] in
/-- Combine the bottom, top and proper-section strata only after they have
all been estimated on the same source and the same comparator. -/
theorem complete_bound {b : ℕ}
    (J : Subgroup (Equiv.Perm (Fin b))) :
    completeQuotientWeight (R := preE7NonPairAction w U) J ≤
      D.mainCoefficient * completeQuotientWeight (R := D.Q) J +
        D.tailCoefficient *
          (2 : ℝ) ^ ((Real.logb 2 3 / 3) * b) := by
  have hsections :
      (∑ i : D.Section, bundledNormalQuotientWeight (D.sectionAxis i) J) ≤
        (∑ i : D.Section, D.sectionCoefficient i) *
          completeQuotientWeight (R := D.Q) J := by
    calc
      (∑ i : D.Section, bundledNormalQuotientWeight (D.sectionAxis i) J) ≤
          ∑ i : D.Section,
            D.sectionCoefficient i *
              completeQuotientWeight (R := D.Q) J := by
        apply Finset.sum_le_sum
        intro i _
        exact D.section_bound i J
      _ = (∑ i : D.Section, D.sectionCoefficient i) *
          completeQuotientWeight (R := D.Q) J := by
        rw [Finset.sum_mul]
  calc
    completeQuotientWeight (R := preE7NonPairAction w U) J ≤
        (Nat.card (GroupEpimorphism J
            (preE7NonPairAction w U)) : ℝ) +
          completeQuotientWeight
            (R := preE7NonPairAction w U ⧸ E block P) J +
          ∑ i : D.Section,
            bundledNormalQuotientWeight (D.sectionAxis i) J :=
      D.stratified_bound J
    _ ≤ (D.tailCoefficient *
            (2 : ℝ) ^ ((Real.logb 2 3 / 3) * b)) +
          (D.topCoefficient *
            completeQuotientWeight (R := D.Q) J) +
          ((∑ i : D.Section, D.sectionCoefficient i) *
            completeQuotientWeight (R := D.Q) J) :=
      add_le_add (add_le_add (D.tail_bound J) (D.top_bound J)) hsections
    _ = D.mainCoefficient * completeQuotientWeight (R := D.Q) J +
          D.tailCoefficient *
            (2 : ℝ) ^ ((Real.logb 2 3 / 3) * b) := by
      unfold mainCoefficient
      ring

/-- Numerical `S3EXC` source obtained from the exact two-sign
stratification.  Using the complete-source interface avoids repeating the
all-normal estimate once for every ambient axis. -/
noncomputable def exceptionalSource
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4) :
    PreE7S3ExceptionalSource w U := by
  have hw : w = 12 := by
    simpa only [hr, hs] using width_eq block
  refine
    { sourceDegree := 10
      sourceDegree_two := by norm_num
      Q := D.Q
      B := D.mainCoefficient
      C := D.tailCoefficient
      eta := 0
      theta := Real.logb 2 3 / 3
      B_nonneg := D.mainCoefficient_nonneg
      C_nonneg := D.tailCoefficient_nonneg
      eta_nonneg := le_rfl
      exponent_margin := by
        rw [hw]
        norm_num [preE7CharacterRho, evenWidth, halfDegree]
      tail_window := logThreeThird_le_window (by rw [hw]; omega)
      complete_bound := by
        intro b J
        simpa only [zero_mul, Real.rpow_zero, mul_one] using
          (DegreeThreeFourBlockTwoSignComparison.complete_bound
            (block := block) (P := P) D J)
      main_menu := ?_
      tail_menu := ?_ }
  · intro b
    calc
      D.mainCoefficient ≤ (2 : ℝ) ^ (384 : ℝ) := D.mainCoefficient_le
      _ ≤ (2 : ℝ) ^ (64 * (w : ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        rw [hw]
        norm_num
      _ ≤ _ := two_rpow_sixtyFour_width_le_menuMass
        (hw.symm ▸ (by norm_num : 8 ≤ 12)) b
  · intro b
    calc
      D.tailCoefficient ≤ (2 : ℝ) ^ (384 : ℝ) := D.tailCoefficient_le
      _ ≤ (2 : ℝ) ^ (64 * (w : ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        rw [hw]
        norm_num
      _ ≤ _ := two_rpow_sixtyFour_width_le_menuMass
        (hw.symm ▸ (by norm_num : 8 ≤ 12)) b

end DegreeThreeFourBlockTwoSignComparison

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
