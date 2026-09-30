import SymmetricSubgroupAsymptotics.C3HighAlignedRefinedContinuation
import SymmetricSubgroupAsymptotics.C3HighAlignedRemainingConsumers
import SymmetricSubgroupAsymptotics.C3CompletePhysicalContinuation
import SymmetricSubgroupAsymptotics.TernaryThreeGroupRankBudgetOwner

/-!
# Every refined aligned high-C3 cell has a local row

After the degree-three ternary cells are removed, a transitive ternary
p-group cell has width nine or twenty seven: widths four, six and twelve are
even and cannot carry a transitive 3-group.  The degree-nine and
degree-twenty-seven rows are installed with constants fixed before the
source degree.  The degree-nine source budget is read from the exact
one-`C3` pattern retained by the cell predicate itself.

Together with the prime-base, natural-`A4`, degree-six and degree-twelve
rows, every refined cell reaches a nonnegative exponentially decaying row.
The high-C3 owner continuation, and with it the complete regular-C3 audit,
therefore close under the named ternary inputs and the Kovács--Praeger
abelianization bound.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

/-- A transitive 3-group has odd degree. -/
theorem transitive_ternaryPGroup_width_not_even {w : ℕ}
    (U : Subgroup (Equiv.Perm (Fin w))) [MulAction.IsPretransitive U (Fin w)]
    (hU : IsPGroup 3 U) (hw : 0 < w) : ¬ 2 ∣ w := by
  intro h2
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hU
  let x : Fin w := ⟨0, hw⟩
  have hdvd : w ∣ Nat.card U := by
    have h := Subgroup.index_dvd_card (MulAction.stabilizer U x)
    rwa [MulAction.index_stabilizer_of_transitive U x, Nat.card_fin] at h
  rw [hk] at hdvd
  have h3 : 2 ∣ 3 := Nat.Prime.dvd_of_dvd_pow Nat.prime_two (h2.trans hdvd)
  omega

/-- The degree-nine ternary p-group row, with its constant fixed before the
source degree and the exact source budget as the only source input. -/
theorem degreeNine_ternaryPGroup_uniform_physical_bound
    (U : Subgroup (Equiv.Perm (Fin 9)))
    [MulAction.IsPretransitive U (Fin 9)] (hU : IsPGroup 3 U) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (b : ℕ) (P : Subgroup (U × Equiv.Perm (Fin b)) → Prop),
      FusionOrbitNatural U P →
      (∀ (N : {N : Subgroup U // N.Normal})
        (J : Subgroup (Equiv.Perm (Fin b))) (β : GroupEpimorphism J (U ⧸ N.1)),
        P (fusionFullGoursatEncode N J β).1 → C1DegreeNineRankBudget J) →
      (Nat.card (FusionOrbitFamily U
          (FusionAcceptedOrbitPredicate U P)) : ℝ) /
          exactBenchmark (b + 9) ≤
        c1EarlierKernel b .degreeNine D
            (Nat.card (Subgroup.normalizer
              (U : Set (Equiv.Perm (Fin 9)))) : ℝ) *
          ((subgroupCount b : ℝ) / exactBenchmark b) := by
  obtain ⟨constant, hconstant, hquotient⟩ :=
    degreeNine_rankBudget_quotientEpimorphism_le_binary U (by simp) hU
  let D : ℝ := Nat.card {N : Subgroup U // N.Normal} * constant
  have hD : 0 ≤ D := mul_nonneg (Nat.cast_nonneg _) hconstant
  refine ⟨D, hD, fun b P hP hSource => ?_⟩
  apply c1EarlierPhysical_owner_bound_of_source_direct .degreeNine U b P hP
    C1DegreeNineRankBudget hSource D hD
  intro J hJ
  have haxis (N : {N : Subgroup U // N.Normal}) :
      fusionSurvivingEpiCount U P N J ≤
        constant * (2 : ℝ) ^ (((8 : ℝ) / 9) * b) := by
    have hsub : Nat.card { β : GroupEpimorphism J (U ⧸ N.1) //
        P (fusionFullGoursatEncode N J β).1 } ≤
        Nat.card (GroupEpimorphism J (U ⧸ N.1)) :=
      Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
    have hsubR : fusionSurvivingEpiCount U P N J ≤
        (Nat.card (GroupEpimorphism J (U ⧸ N.1)) : ℝ) := by
      unfold fusionSurvivingEpiCount
      exact_mod_cast hsub
    exact hsubR.trans
      (hquotient (QuotientGroup.mk' N.1)
        (QuotientGroup.mk'_surjective N.1) b J hJ)
  have hE : (0 : ℝ) ≤ (2 : ℝ) ^ (((8 : ℝ) / 9) * b) := by positivity
  have hb : (1 : ℝ) ≤ (b : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) b]
  calc
    (∑ N : {N : Subgroup U // N.Normal},
        fusionSurvivingEpiCount U P N J) ≤
        ∑ _N : {N : Subgroup U // N.Normal},
          constant * (2 : ℝ) ^ (((8 : ℝ) / 9) * b) :=
      Finset.sum_le_sum (fun N _ => haxis N)
    _ = D * (2 : ℝ) ^ (((8 : ℝ) / 9) * b) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Fintype.card_eq_nat_card]
      dsimp only [D]
      ring
    _ ≤ D * ((b : ℝ) + 1) * (2 : ℝ) ^ (((8 : ℝ) / 9) * b) := by
      have h := mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hE hb) hD
      calc D * (2 : ℝ) ^ (((8 : ℝ) / 9) * b) ≤
            D * (((b : ℝ) + 1) * (2 : ℝ) ^ (((8 : ℝ) / 9) * b)) := h
        _ = D * ((b : ℝ) + 1) * (2 : ℝ) ^ (((8 : ℝ) / 9) * b) := by ring
    _ = D * ((b : ℝ) + 1) *
        (2 : ℝ) ^ (c1EarlierExponent .degreeNine * b) := by
      rfl

/-- The degree-twenty-seven ternary p-group row, with its constant fixed
before the source degree. -/
theorem degreeTwentySeven_ternaryPGroup_uniform_physical_bound
    (U : Subgroup (Equiv.Perm (Fin 27)))
    [MulAction.IsPretransitive U (Fin 27)] (hU : IsPGroup 3 U) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (b : ℕ) (P : Subgroup (U × Equiv.Perm (Fin b)) → Prop),
      FusionOrbitNatural U P →
      (Nat.card (FusionOrbitFamily U
          (FusionAcceptedOrbitPredicate U P)) : ℝ) /
          exactBenchmark (b + 27) ≤
        c1EarlierKernel b .degreeTwentySeven D
            (Nat.card (Subgroup.normalizer
              (U : Set (Equiv.Perm (Fin 27)))) : ℝ) *
          ((subgroupCount b : ℝ) / exactBenchmark b) := by
  obtain ⟨constant, hconstant, hquotient⟩ :=
    degreeTwentySeven_quotientEpimorphism_le_binary U (by simp) hU
  exact c1EarlierPhysical_owner_bound_of_quotientConstants .degreeTwentySeven U
    (fun N _ => ⟨constant, hconstant, fun b J =>
      hquotient (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) b J⟩)

/-- Every aligned ternary p-group cell of width other than three has a local
row: width nine through the retained source budget, width twenty seven
unconditionally. -/
theorem c3HighAligned_ternaryPGroup_localRow
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    (j : C3HighAlignedFirstOwnerIndex)
    (hk : c3PhysicalOwnerKindEquiv j.1.2.1 =
      C3PhysicalOwnerKind.ternaryPGroup)
    (hw : c3HighAlignedFirstOwnerWidth j ≠ 3) :
    C3HighAlignedLocalRow j := by
  rcases j with ⟨⟨d, owner, i⟩, hj⟩
  have hU := hj.2
  rw [hk] at hU
  letI := Non2TransitiveActionClass.representative_pretransitive i
  cases d with
  | three => exact absurd rfl hw
  | four =>
      let U : Subgroup (Equiv.Perm (Fin 4)) := i.representative
      letI : MulAction.IsPretransitive U (Fin 4) :=
        Non2TransitiveActionClass.representative_pretransitive i
      exact absurd (by decide : 2 ∣ 4)
        (transitive_ternaryPGroup_width_not_even U hU (by decide))
  | six =>
      let U : Subgroup (Equiv.Perm (Fin 6)) := i.representative
      letI : MulAction.IsPretransitive U (Fin 6) :=
        Non2TransitiveActionClass.representative_pretransitive i
      exact absurd (by decide : 2 ∣ 6)
        (transitive_ternaryPGroup_width_not_even U hU (by decide))
  | twelve =>
      let U : Subgroup (Equiv.Perm (Fin 12)) := i.representative
      letI : MulAction.IsPretransitive U (Fin 12) :=
        Non2TransitiveActionClass.representative_pretransitive i
      exact absurd (by decide : 2 ∣ 12)
        (transitive_ternaryPGroup_width_not_even U hU (by decide))
  | nine =>
      let U : Subgroup (Equiv.Perm (Fin 9)) := i.representative
      letI : MulAction.IsPretransitive U (Fin 9) :=
        Non2TransitiveActionClass.representative_pretransitive i
      obtain ⟨D, hD, hphys⟩ := degreeNine_ternaryPGroup_uniform_physical_bound U hU
      apply C3HighAlignedLocalRow.of_kernel _ .degreeNine D hD
      intro n hn
      have hbn : n - 9 + 9 = n := Nat.sub_add_cancel hn
      have hmain := hphys (n - 9)
        (c3HighFirstOwnerPredicate ⟨C3HighWidthLabel.nine, owner, i⟩ (n - 9))
        (c3HighFirstOwnerPredicate_natural ⟨C3HighWidthLabel.nine, owner, i⟩ (n - 9))
        (fun N J β hP => C1DegreeNineSourcePattern.rankBudget hChief hPrimitive h18 J
          (c3HighFirstOwnerPredicate_sourcePattern ⟨C3HighWidthLabel.nine, owner, i⟩
            (by simp [c3HighFirstOwnerWidth, C3HighWidthLabel.width]) (n - 9) N J β hP))
      rw [hbn] at hmain
      rw [fusionWidthCanonicalFamily_card]
      exact hmain
  | twentySeven =>
      let U : Subgroup (Equiv.Perm (Fin 27)) := i.representative
      letI : MulAction.IsPretransitive U (Fin 27) :=
        Non2TransitiveActionClass.representative_pretransitive i
      obtain ⟨D, hD, hphys⟩ := degreeTwentySeven_ternaryPGroup_uniform_physical_bound U hU
      apply C3HighAlignedLocalRow.of_kernel _ .degreeTwentySeven D hD
      intro n hn
      have hbn : n - 27 + 27 = n := Nat.sub_add_cancel hn
      have hmain := hphys (n - 27)
        (c3HighFirstOwnerPredicate ⟨C3HighWidthLabel.twentySeven, owner, i⟩ (n - 27))
        (c3HighFirstOwnerPredicate_natural ⟨C3HighWidthLabel.twentySeven, owner, i⟩ (n - 27))
      rw [hbn] at hmain
      rw [fusionWidthCanonicalFamily_card]
      exact hmain

/-- Exhaustion: every refined aligned cell reaches one of the ternary
p-group, natural-`A4`, degree-six, prime-base or binary-nine rows. -/
theorem c3HighRefinedAligned_localRow
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    (hKP : KovacsPraegerAbelianizationBound)
    (j : C3HighRefinedAlignedIndex) :
    C3HighAlignedLocalRow j.1 := by
  obtain ⟨j, hj⟩ := j
  cases hk : c3PhysicalOwnerKindEquiv j.1.2.1 with
  | ternaryPGroup =>
      exact c3HighAligned_ternaryPGroup_localRow hChief hPrimitive h18 j hk
        (fun hw => hj ⟨hw, hk⟩)
  | naturalA4 => exact c3HighAligned_naturalA4_localRow j hk
  | degreeSix =>
      obtain ⟨D, hD, h⟩ := c3HighAligned_degreeSix_local_bound hPrimitive hKP j hk
      exact C3HighAlignedLocalRow.of_kernel j .degreeSix D hD h
  | degreeTwelve =>
      obtain ⟨r, D, hD, h⟩ :=
        c3HighAligned_degreeTwelve_local_bound hChief hWeight hPrimitive h18 j hk
      exact C3HighAlignedLocalRow.of_kernel j r D hD h

/-- The complete high-C3 structural-owner continuation, with no remaining
local-row hypothesis. -/
noncomputable def c3PhysicalStructuralOwner_closedExponentialForwardEstimate
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    (hKP : KovacsPraegerAbelianizationBound) :
    OrdinaryFrontierClosure.ExponentialForwardEstimate
      c3PhysicalStructuralOwnerRatio :=
  let hrow := c3HighRefinedAligned_localRow hChief hWeight hPrimitive h18 hKP
  c3PhysicalStructuralOwner_refinedExponentialForwardEstimate
    hChief hWeight hPrimitive h18
    (fun j => Classical.choose (hrow j))
    (fun j => (Classical.choose_spec (hrow j)).1)
    (fun j => (Classical.choose_spec (hrow j)).2.1)
    (fun j => (Classical.choose_spec (hrow j)).2.2)

/-- The complete regular-C3 ordinary audit: the closed high-owner
continuation together with the closed residual row. -/
noncomputable def c3CompleteOrdinary_closedExponentialForwardEstimate
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    (hKP : KovacsPraegerAbelianizationBound) :
    OrdinaryFrontierClosure.ExponentialForwardEstimate
      c3CompleteOrdinaryRatio :=
  OrdinaryFrontierClosure.ExponentialForwardEstimate.of_le
    (OrdinaryFrontierClosure.ExponentialForwardEstimate.add
      (c3PhysicalStructuralOwner_closedExponentialForwardEstimate
        hChief hWeight hPrimitive h18 hKP)
      (c3FinalResidual_exponentialForwardEstimate hChief hWeight hPrimitive h18))
    3 c3CompleteOrdinaryRatio_le_owner_add_residual

end SymmetricSubgroupAsymptotics

end
