import SymmetricSubgroupAsymptotics.C3TernaryPGroupAlignedPositiveLocal
import SymmetricSubgroupAsymptotics.C1DegreeNineRankBudgetWithoutCatalogue

/-! The old positive degree9 ternary row uses the same surviving source
pattern and its newly proved exact rank budget. -/
set_option autoImplicit false
noncomputable section
attribute [-instance] SymmetricSubgroupAsymptotics.originalNormalFintype
open Filter
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics
/-- The unrestricted aligned degree-nine cell has the sharp ternary p-group
row: its retained source pattern implies the numerical rank budget on every
surviving quotient map. -/
theorem c3HighAligned_degreeNine_unrestricted_local_bound_without_catalogue
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hgen : PrimitiveNormalGeneratorInput)
    (hindex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    (h18 : DegreeEighteenTernaryHeadBound)
    (j : C3HighAlignedFirstOwnerIndex)
    (hkind : c3PhysicalOwnerKindEquiv j.1.2.1 =
      C3PhysicalOwnerKind.ternaryPGroup)
    (hwidth : c3HighAlignedFirstOwnerWidth j = 9) :
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ (n : ℕ) (hn : c3HighAlignedFirstOwnerWidth j ≤ n),
      (Nat.card (FusionWidthCanonicalFamily
        (c3HighAlignedFirstOwnerAction j) hn
        (c3HighAlignedFirstOwnerPredicate j
          (n - c3HighAlignedFirstOwnerWidth j))) : ℝ) /
          exactBenchmark n ≤
        c1EarlierKernel (n - c3HighAlignedFirstOwnerWidth j) .degreeNine D
            (Nat.card (Subgroup.normalizer
              (c3HighAlignedFirstOwnerAction j :
                Set (Equiv.Perm (Fin (c3HighAlignedFirstOwnerWidth j))))) : ℝ) *
          ordinarySubgroupRatio (n - c3HighAlignedFirstOwnerWidth j) := by
  rcases j with ⟨⟨d, owner, i⟩, hj⟩
  cases d with
  | three => simp [c3HighAlignedFirstOwnerWidth, c3HighFirstOwnerWidth,
      C3HighWidthLabel.width] at hwidth
  | four => simp [c3HighAlignedFirstOwnerWidth, c3HighFirstOwnerWidth,
      C3HighWidthLabel.width] at hwidth
  | six => simp [c3HighAlignedFirstOwnerWidth, c3HighFirstOwnerWidth,
      C3HighWidthLabel.width] at hwidth
  | twelve => simp [c3HighAlignedFirstOwnerWidth, c3HighFirstOwnerWidth,
      C3HighWidthLabel.width] at hwidth
  | twentySeven => simp [c3HighAlignedFirstOwnerWidth, c3HighFirstOwnerWidth,
      C3HighWidthLabel.width] at hwidth
  | nine =>
      let U : Subgroup (Equiv.Perm (Fin 9)) := i.representative
      letI : MulAction.IsPretransitive U (Fin 9) := by
        simpa only [U, C3HighWidthLabel.width] using
          (Non2TransitiveActionClass.representative_pretransitive i)
      have hU : IsPGroup 3 U := by
        have h := hj.2
        rw [hkind] at h
        simpa only [U, C3PhysicalOwnerKind.property,
          c3HighFirstOwnerAction, c3HighFirstOwnerWidth,
          C3HighWidthLabel.width] using h
      obtain ⟨constant, hconstant, hquotient⟩ :=
        degreeNine_rankBudget_quotientEpimorphism_le_binary
          U (by simp) hU
      let D : ℝ :=
        Nat.card {N : Subgroup U // N.Normal} * constant
      have hD : 0 ≤ D := mul_nonneg (Nat.cast_nonneg _) hconstant
      refine ⟨D, hD, fun n hn => ?_⟩
      let b := n - 9
      have hphysical :
          (Nat.card (FusionOrbitFamily U
            (FusionAcceptedOrbitPredicate U
              (c3HighFirstOwnerPredicate
                ⟨C3HighWidthLabel.nine, owner, i⟩ b))) : ℝ) /
              exactBenchmark (b + 9) ≤
            c1EarlierKernel b .degreeNine D
                (Nat.card (Subgroup.normalizer
                  (U : Set (Equiv.Perm (Fin 9)))) : ℝ) *
              ((subgroupCount b : ℝ) / exactBenchmark b) := by
        apply c1EarlierPhysical_owner_bound_of_source_direct .degreeNine
          U b
          (c3HighFirstOwnerPredicate
            ⟨C3HighWidthLabel.nine, owner, i⟩ b)
          (c3HighFirstOwnerPredicate_natural
            ⟨C3HighWidthLabel.nine, owner, i⟩ b)
          C1DegreeNineRankBudget
          (fun N J beta hP =>
            (c3HighFirstOwnerPredicate_sourcePattern
              ⟨C3HighWidthLabel.nine, owner, i⟩
              (by simp [c3HighFirstOwnerWidth, C3HighWidthLabel.width])
              b N J beta hP).rankBudget_without_catalogue hChief hgen hindex published8 h18 J)
          D hD
        intro J hJ
        have haxis (N : {N : Subgroup U // N.Normal}) :
            fusionSurvivingEpiCount U
                (c3HighFirstOwnerPredicate
                  ⟨C3HighWidthLabel.nine, owner, i⟩ b) N J ≤
              constant * (2 : ℝ) ^ (((8 : ℝ) / 9) * b) := by
          have hsub : Nat.card {beta : GroupEpimorphism J
              (U ⧸ N.1) //
              c3HighFirstOwnerPredicate
                ⟨C3HighWidthLabel.nine, owner, i⟩ b
                (fusionFullGoursatEncode N J beta).1} ≤
              Nat.card (GroupEpimorphism J (U ⧸ N.1)) :=
            Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
          have hsubR : fusionSurvivingEpiCount U
              (c3HighFirstOwnerPredicate
                ⟨C3HighWidthLabel.nine, owner, i⟩ b) N J ≤
                (Nat.card (GroupEpimorphism J
                  (U ⧸ N.1)) : ℝ) := by
            unfold fusionSurvivingEpiCount
            exact_mod_cast hsub
          exact hsubR.trans
            (hquotient (QuotientGroup.mk' N.1)
              (QuotientGroup.mk'_surjective N.1) b J hJ)
        calc
          (∑ N : {N : Subgroup U // N.Normal},
              fusionSurvivingEpiCount U
                (c3HighFirstOwnerPredicate
                  ⟨C3HighWidthLabel.nine, owner, i⟩ b) N J) ≤
              ∑ _N : {N : Subgroup U // N.Normal},
                constant * (2 : ℝ) ^ (((8 : ℝ) / 9) * b) :=
            Finset.sum_le_sum (fun N _ => haxis N)
          _ = D * (2 : ℝ) ^ (((8 : ℝ) / 9) * b) := by
            simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
              Fintype.card_eq_nat_card]
            dsimp only [D]
            ring
          _ ≤ D * ((b : ℝ) + 1) *
              (2 : ℝ) ^ (((8 : ℝ) / 9) * b) := by
            have hb : (1 : ℝ) ≤ (b : ℝ) + 1 := by
              linarith [Nat.cast_nonneg (α := ℝ) b]
            calc
              D * (2 : ℝ) ^ (((8 : ℝ) / 9) * b) =
                  (D * 1) * (2 : ℝ) ^ (((8 : ℝ) / 9) * b) := by ring
              _ ≤ (D * ((b : ℝ) + 1)) *
                  (2 : ℝ) ^ (((8 : ℝ) / 9) * b) := by gcongr
              _ = _ := by ring
          _ = D * ((b : ℝ) + 1) *
              (2 : ℝ) ^ (c1EarlierExponent .degreeNine * b) := by rfl
      rw [fusionWidthCanonicalFamily_card]
      have hbn : b + 9 = n := Nat.sub_add_cancel (by
        simpa [c3HighAlignedFirstOwnerWidth, c3HighFirstOwnerWidth,
          C3HighWidthLabel.width] using hn)
      rw [hbn] at hphysical
      simpa only [U, c3HighAlignedFirstOwnerAction,
        c3HighAlignedFirstOwnerWidth, c3HighAlignedFirstOwnerPredicate,
        c3HighFirstOwnerAction, c3HighFirstOwnerWidth,
        C3HighWidthLabel.width, b, ordinarySubgroupRatio] using hphysical

/-- The unrestricted degree-nine estimate packaged in the common aligned
local-row interface. -/
theorem c3HighAligned_degreeNine_ternaryPGroup_localRow_without_catalogue
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hgen : PrimitiveNormalGeneratorInput)
    (hindex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    (h18 : DegreeEighteenTernaryHeadBound)
    (j : C3HighAlignedFirstOwnerIndex)
    (hkind : c3PhysicalOwnerKindEquiv j.1.2.1 =
      C3PhysicalOwnerKind.ternaryPGroup)
    (hwidth : c3HighAlignedFirstOwnerWidth j = 9) :
    C3HighAlignedLocalRow j := by
  obtain ⟨D, hD, h⟩ :=
    c3HighAligned_degreeNine_unrestricted_local_bound_without_catalogue
      hChief hgen hindex published8 h18 j hkind hwidth
  exact C3HighAlignedLocalRow.of_kernel j .degreeNine D hD h

end SymmetricSubgroupAsymptotics
