import SymmetricSubgroupAsymptotics.C3DegreeTwelveAlignedLocal
import SymmetricSubgroupAsymptotics.C1BinaryNineRegularTopWithoutCatalogue
import SymmetricSubgroupAsymptotics.DegreeTwelveImprimitiveTopGeometryWithoutCatalogue
import SymmetricSubgroupAsymptotics.TernaryHighEarlierOwnerSoluble

/-! Earlier aligned degree12 cells are actually imprimitive; retain their
same literal top geometry and the unchanged mixed source-pattern row. -/
set_option autoImplicit false
noncomputable section
open Filter
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics
/-- The literal top geometry of an aligned degree-twelve action installs
either the prime-base owner or the complete mixed binary-nine row. -/
theorem degreeTwelve_alignedAction_primeBase_or_binaryNine_without_catalogue
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hgen : PrimitiveNormalGeneratorInput)
    (hindex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    (h18 : DegreeEighteenTernaryHeadBound)
    (U : Subgroup (Equiv.Perm (Fin 12))) [MulAction.IsPretransitive U (Fin 12)]
    (hU : C3HighAlignedAction U) :
    IsC1TernaryPrimeBaseOwner U ∨
      ∃ D : ℝ, 0 ≤ D ∧ ∀ (b : ℕ) (P : Subgroup (U × Equiv.Perm (Fin b)) → Prop),
        FusionOrbitNatural U P →
        (∀ (N : {N : Subgroup U // N.Normal})
          (J : Subgroup (Equiv.Perm (Fin b))) (β : GroupEpimorphism J (U ⧸ N.1)),
          P (fusionFullGoursatEncode N J β).1 → C1DegreeNineSourcePattern J) →
        (Nat.card (FusionOrbitFamily U (FusionAcceptedOrbitPredicate U P)) : ℝ) /
            exactBenchmark (b + 12) ≤
          c1EarlierKernel b .degreeTwelveMixed D
            (Nat.card (Subgroup.normalizer (U : Set (Equiv.Perm (Fin 12)))) : ℝ) *
            ((subgroupCount b : ℝ) / exactBenchmark b) := by
  obtain ⟨N0, hN0, hHigh, hEarlier⟩ := hU
  letI := hN0
  have hHigh' : 3 * Nat.card (Fin 12) <
      20 * Module.finrank (ZMod 3) (primeRelativeCharacters 3 N0) := by
    simpa using hHigh
  obtain ⟨ω₀, D, c, horient, hc, hTopRank, hRank⟩ :=
    degreeTwelve_high_imprimitive_top_geometry_without_catalogue
      hChief hWeight hgen hindex published8 h18
      (A := U) (Ω := Fin 12) N0
      (hEarlier.degreeTwelve_imprimitive hindex (by simp)) (by simp) hHigh'
  letI : Fintype D.Points := Fintype.ofFinite D.Points
  letI : ∀ x : D.Points, Fintype (originalBlockFibre D.map x) :=
    fun x => Fintype.ofFinite (originalBlockFibre D.map x)
  rcases horient with h34 | h43
  · exact Or.inl (D.degreeTwelve_primeBase_owner N0 h34.1 h34.2.2 hRank hTopRank)
  · have hCard : ∀ x : D.Points, Nat.card (originalBlockFibre D.map x) = 4 := by
      intro x
      rw [D.originalBlockFibre_card_eq x, h43.1]
    let e : ∀ x : D.Points, Fin 4 ≃ originalBlockFibre D.map x :=
      fun x => (Finite.equivFinOfCardEq (hCard x)).symm
    let W := D.fourByThree_nineTopOwnerWitness N0 c h43.2.1 h43.2.2 hc hTopRank hRank e
    exact Or.inr
      (C1BinaryNineTopOwnerWitness.physical_owner_bound_ternaryTop_without_catalogue hChief hgen hindex published8 h18
        U W (fun N => by
          letI : N.1.Normal := N.2
          exact D.fourByThree_nineTopOwnerWitness_regular N0 c h43.2.1 h43.2.2 hc
            hTopRank hRank e N.1))

/-- An aligned degree-twelve cell satisfies the prime-base row or the mixed
binary-nine row, selected by the literal top geometry of its action. -/
theorem c3HighAligned_degreeTwelve_local_bound_without_catalogue
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hgen : PrimitiveNormalGeneratorInput)
    (hindex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    (h18 : DegreeEighteenTernaryHeadBound)
    (j : C3HighAlignedFirstOwnerIndex)
    (hkind : c3PhysicalOwnerKindEquiv j.1.2.1 =
      C3PhysicalOwnerKind.degreeTwelve) :
    ∃ (r : C1EarlierRow) (D : ℝ), 0 ≤ D ∧
      ∀ (n : ℕ) (hn : c3HighAlignedFirstOwnerWidth j ≤ n),
      (Nat.card (FusionWidthCanonicalFamily
        (c3HighAlignedFirstOwnerAction j) hn
        (c3HighAlignedFirstOwnerPredicate j
          (n - c3HighAlignedFirstOwnerWidth j))) : ℝ) /
          exactBenchmark n ≤
        c1EarlierKernel (n - c3HighAlignedFirstOwnerWidth j) r D
            (Nat.card (Subgroup.normalizer
              (c3HighAlignedFirstOwnerAction j :
                Set (Equiv.Perm (Fin (c3HighAlignedFirstOwnerWidth j))))) : ℝ) *
          ordinarySubgroupRatio (n - c3HighAlignedFirstOwnerWidth j) := by
  rcases j with ⟨⟨d, owner, i⟩, hj⟩
  have hcard := hj.2
  rw [hkind] at hcard
  change Nat.card (Fin d.width) = 12 at hcard
  simp only [Nat.card_fin] at hcard
  cases d with
  | three => simp [C3HighWidthLabel.width] at hcard
  | four => simp [C3HighWidthLabel.width] at hcard
  | six => simp [C3HighWidthLabel.width] at hcard
  | nine => simp [C3HighWidthLabel.width] at hcard
  | twentySeven => simp [C3HighWidthLabel.width] at hcard
  | twelve =>
      let U : Subgroup (Equiv.Perm (Fin 12)) := i.representative
      letI : MulAction.IsPretransitive U (Fin 12) :=
        Non2TransitiveActionClass.representative_pretransitive i
      rcases degreeTwelve_alignedAction_primeBase_or_binaryNine_without_catalogue hChief hWeight hgen hindex published8 h18
          U hj.1 with hPrime | ⟨Dc, hDc, hphys⟩
      · obtain ⟨W⟩ := hPrime
        exact ⟨.degreeTwelve, _,
          Finset.sum_nonneg (fun N _ => mul_nonneg (Nat.cast_nonneg _)
            (le_trans zero_le_one (le_max_left _ _))),
          c3HighAligned_primeBase_local_bound ⟨⟨C3HighWidthLabel.twelve, owner, i⟩, hj⟩
            hkind W⟩
      · refine ⟨.degreeTwelveMixed, Dc, hDc, fun n hn => ?_⟩
        have hbn : n - 12 + 12 = n := Nat.sub_add_cancel hn
        have hmain := hphys (n - 12)
          (c3HighFirstOwnerPredicate ⟨C3HighWidthLabel.twelve, owner, i⟩ (n - 12))
          (c3HighFirstOwnerPredicate_natural ⟨C3HighWidthLabel.twelve, owner, i⟩ (n - 12))
          (fun N J β hP => c3HighFirstOwnerPredicate_sourcePattern
            ⟨C3HighWidthLabel.twelve, owner, i⟩
            (by simp [c3HighFirstOwnerWidth, C3HighWidthLabel.width]) (n - 12) N J β hP)
        rw [hbn] at hmain
        rw [fusionWidthCanonicalFamily_card]
        exact hmain

end SymmetricSubgroupAsymptotics

end
