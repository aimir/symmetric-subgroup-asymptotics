import SymmetricSubgroupAsymptotics.CFSGSufficientC1DegreeNineCapacity
import SymmetricSubgroupAsymptotics.CFSGSufficientTernaryOwnerExhaustion
import SymmetricSubgroupAsymptotics.C3PhysicalOwnerBranchesWithoutCatalogue
import SymmetricSubgroupAsymptotics.C3DegreeSixAlignedLocalWithoutCatalogue
import SymmetricSubgroupAsymptotics.C3DegreeTwelveAlignedLocalWithoutCatalogue
import SymmetricSubgroupAsymptotics.C3TernaryPGroupAlignedPositiveLocalWithoutCatalogue
import SymmetricSubgroupAsymptotics.C3HighAlignedRefinedContinuationWithoutCatalogue
import SymmetricSubgroupAsymptotics.C3HighAlignedRefinedExhaustionWithoutCatalogue

/-! Proof-only sufficient-index forwarding on the unchanged actual source
families. All original normal subgroups, complement actions, numerical
rows and rank predicates are retained; no sharp universal hSI is produced. -/

/-! The unchanged four old owner branches cover the actual old-owner sector,
using the proved bounded menu rather than a global strict-head premise. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics
/-- The strict high inequality classifies every complete physical owner into
one of the four action branches. -/
theorem c3PhysicalStructuralOwner_branch_cover_of_sufficient
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hgen : PrimitiveNormalGeneratorInput)
    (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    (h18 : DegreeEighteenTernaryHeadBound)
    {n : ℕ} {G : Subgroup (Equiv.Perm (Fin n))}
    (hG : C3PhysicalStructuralOwner n G) :
    ∃ k, C3PhysicalStructuralOwnerBranch k n G := by
  rcases hG with ⟨b, e, H, hphysical, hfull, o, N, hN, hHigh, hOwner⟩
  let A := OrbitProfileFromOrbits.orbitImage (C3ComplementSource b H) o
  letI : MulAction.IsPretransitive A o.orbit :=
    orbitImage_pretransitive (C3ComplementSource b H) o
  letI : N.Normal := hN
  rcases ternaryHigh_earlierOwner_owned_menu_of_sufficient hChief hWeight hgen hindex published8 h18
      (A := A) (X := o.orbit) N hHigh hOwner with hThree | hA4 | hSix | hTwelve
  · exact ⟨.ternaryPGroup,
      b, e, H, hphysical, hfull, o, N, hN, hHigh, hOwner, hThree⟩
  · exact ⟨.naturalA4,
      b, e, H, hphysical, hfull, o, N, hN, hHigh, hOwner, hA4⟩
  · exact ⟨.degreeSix,
      b, e, H, hphysical, hfull, o, N, hN, hHigh, hOwner, hSix⟩
  · exact ⟨.degreeTwelve,
      b, e, H, hphysical, hfull, o, N, hN, hHigh, hOwner, hTwelve⟩

theorem c3PhysicalStructuralBranchMenu_cover_of_sufficient
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hgen : PrimitiveNormalGeneratorInput)
    (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    (h18 : DegreeEighteenTernaryHeadBound)
    {n : ℕ} {G : Subgroup (Equiv.Perm (Fin n))}
    (hG : C3PhysicalStructuralOwner n G) :
    ∃ i, c3PhysicalStructuralBranchMenu n i G := by
  obtain ⟨k, hk⟩ := c3PhysicalStructuralOwner_branch_cover_of_sufficient
    hChief hWeight hgen hindex published8 h18 hG
  exact ⟨c3PhysicalOwnerKindEquiv.symm k, by
    simpa only [c3PhysicalStructuralBranchMenu,
      Equiv.apply_symm_apply] using hk⟩

end SymmetricSubgroupAsymptotics


/-! The unchanged aligned six-point physical row consumes only the proved
actual six-point owner split. -/
set_option autoImplicit false
noncomputable section
open Filter
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics
theorem degreeSix_alignedAction_quotientConstants_of_sufficient
    (hgen : PrimitiveNormalGeneratorInput)
    (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    (hKP : KovacsPraegerAbelianizationBound)
    (U : Subgroup (Equiv.Perm (Fin 6))) [MulAction.IsPretransitive U (Fin 6)]
    (hU : C3HighAlignedAction U) :
    ∀ (N : Subgroup U) [N.Normal], ∃ C : ℝ, 0 ≤ C ∧
      ∀ (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b))),
        (Nat.card (GroupEpimorphism J (U ⧸ N)) : ℝ) ≤
          C * (2 : ℝ) ^ ((8 / 15 : ℝ) * b) := by
  obtain ⟨N0, hN0, hHigh, _⟩ := hU
  letI := hN0
  have hHigh' : 3 * Nat.card (Fin 6) <
      20 * Module.finrank (ZMod 3) (primeRelativeCharacters 3 N0) := by
    simpa using hHigh
  rcases degreeSix_high_oddIndexOwner_or_binaryBlock_of_sufficient hgen hindex published8 (A := U) (Ω := Fin 6)
      N0 (by simp) hHigh' with hOdd | ⟨ω₀, D, hFibre, hPoints⟩
  · obtain ⟨W⟩ := hOdd
    intro N hN
    refine ⟨(Nat.card (U ≃* U) : ℝ) + Nat.card ((U ⧸ N) ≃* (U ⧸ N)) + 1,
      by positivity, fun b J => ?_⟩
    exact W.quotientEpimorphism_bound hKP (by simp) N b J
  · let points : D.Points ≃ Fin 3 := Finite.equivFinOfCardEq hPoints
    let F := D.binaryBlockFrame hFibre points
    have hTop : Nat.card F.top.range = 3 :=
      D.binaryBlockFrame_top_card N0 hFibre hPoints hHigh' points
    obtain ⟨B⟩ := F.blockCoordinates_nonempty hTop
    apply quotientConstants_of_mulEquiv D.originalPermutationEquiv
    intro M hM
    refine ⟨(Nat.card ((D.originalPermutationImage ⧸ M) ≃*
        (D.originalPermutationImage ⧸ M)) : ℝ) + 1, by positivity, fun b J => ?_⟩
    exact B.quotientEpimorphism_bound M hKP b J

/-- The complete physical degree-six row on an aligned selected action. -/
theorem degreeSix_alignedAction_physical_owner_bound_of_sufficient
    (hgen : PrimitiveNormalGeneratorInput)
    (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    (hKP : KovacsPraegerAbelianizationBound)
    (U : Subgroup (Equiv.Perm (Fin 6))) [MulAction.IsPretransitive U (Fin 6)]
    (hU : C3HighAlignedAction U) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (b : ℕ) (P : Subgroup (U × Equiv.Perm (Fin b)) → Prop),
      FusionOrbitNatural U P →
      (Nat.card (FusionOrbitFamily U (FusionAcceptedOrbitPredicate U P)) : ℝ) /
          exactBenchmark (b + 6) ≤
        c1EarlierKernel b .degreeSix D
            (Nat.card (Subgroup.normalizer (U : Set (Equiv.Perm (Fin 6)))) : ℝ) *
          ((subgroupCount b : ℝ) / exactBenchmark b) :=
  c1EarlierPhysical_owner_bound_of_quotientConstants .degreeSix U
    (degreeSix_alignedAction_quotientConstants_of_sufficient hgen hindex published8 hKP U hU)

/-- An aligned degree-six cell, whether its intrinsic owner is the
odd-index-two owner or the cyclic binary-module owner, satisfies the
degree-six row in the exact form consumed by the aligned continuation. -/
theorem c3HighAligned_degreeSix_local_bound_of_sufficient
    (hgen : PrimitiveNormalGeneratorInput)
    (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    (hKP : KovacsPraegerAbelianizationBound)
    (j : C3HighAlignedFirstOwnerIndex)
    (hkind : c3PhysicalOwnerKindEquiv j.1.2.1 =
      C3PhysicalOwnerKind.degreeSix) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (n : ℕ) (hn : c3HighAlignedFirstOwnerWidth j ≤ n),
      (Nat.card (FusionWidthCanonicalFamily
        (c3HighAlignedFirstOwnerAction j) hn
        (c3HighAlignedFirstOwnerPredicate j
          (n - c3HighAlignedFirstOwnerWidth j))) : ℝ) /
          exactBenchmark n ≤
        c1EarlierKernel (n - c3HighAlignedFirstOwnerWidth j) .degreeSix D
            (Nat.card (Subgroup.normalizer
              (c3HighAlignedFirstOwnerAction j :
                Set (Equiv.Perm (Fin (c3HighAlignedFirstOwnerWidth j))))) : ℝ) *
          ordinarySubgroupRatio (n - c3HighAlignedFirstOwnerWidth j) := by
  rcases j with ⟨⟨d, owner, i⟩, hj⟩
  have hcard := hj.2
  rw [hkind] at hcard
  change Nat.card (Fin d.width) = 6 at hcard
  simp only [Nat.card_fin] at hcard
  cases d with
  | three => simp [C3HighWidthLabel.width] at hcard
  | four => simp [C3HighWidthLabel.width] at hcard
  | nine => simp [C3HighWidthLabel.width] at hcard
  | twelve => simp [C3HighWidthLabel.width] at hcard
  | twentySeven => simp [C3HighWidthLabel.width] at hcard
  | six =>
      let U : Subgroup (Equiv.Perm (Fin 6)) := i.representative
      letI : MulAction.IsPretransitive U (Fin 6) :=
        Non2TransitiveActionClass.representative_pretransitive i
      obtain ⟨D, hD, hphys⟩ := degreeSix_alignedAction_physical_owner_bound_of_sufficient
        hgen hindex published8 hKP U hj.1
      refine ⟨D, hD, fun n hn => ?_⟩
      have hbn : n - 6 + 6 = n := Nat.sub_add_cancel hn
      have hmain := hphys (n - 6)
        (c3HighFirstOwnerPredicate ⟨C3HighWidthLabel.six, owner, i⟩ (n - 6))
        (c3HighFirstOwnerPredicate_natural ⟨C3HighWidthLabel.six, owner, i⟩ (n - 6))
      rw [hbn] at hmain
      rw [fusionWidthCanonicalFamily_card]
      exact hmain

end SymmetricSubgroupAsymptotics

end


/-! Earlier aligned degree12 cells are actually imprimitive; retain their
same literal top geometry and the unchanged mixed source-pattern row. -/
set_option autoImplicit false
noncomputable section
open Filter
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics
/-- The literal top geometry of an aligned degree-twelve action installs
either the prime-base owner or the complete mixed binary-nine row. -/
theorem degreeTwelve_alignedAction_primeBase_or_binaryNine_of_sufficient
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hgen : PrimitiveNormalGeneratorInput)
    (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
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
    degreeTwelve_high_imprimitive_top_geometry_of_sufficient
      hChief hWeight hgen hindex published8 h18
      (A := U) (Ω := Fin 12) N0
      (hEarlier.degreeTwelve_imprimitive_of_sufficient hindex (by simp)) (by simp) hHigh'
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
      (C1BinaryNineTopOwnerWitness.physical_owner_bound_ternaryTop_of_sufficient hChief hgen hindex published8 h18
        U W (fun N => by
          letI : N.1.Normal := N.2
          exact D.fourByThree_nineTopOwnerWitness_regular N0 c h43.2.1 h43.2.2 hc
            hTopRank hRank e N.1))

/-- An aligned degree-twelve cell satisfies the prime-base row or the mixed
binary-nine row, selected by the literal top geometry of its action. -/
theorem c3HighAligned_degreeTwelve_local_bound_of_sufficient
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hgen : PrimitiveNormalGeneratorInput)
    (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
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
      rcases degreeTwelve_alignedAction_primeBase_or_binaryNine_of_sufficient hChief hWeight hgen hindex published8 h18
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
theorem c3HighAligned_degreeNine_unrestricted_local_bound_of_sufficient
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hgen : PrimitiveNormalGeneratorInput)
    (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
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
              b N J beta hP).rankBudget_of_sufficient hChief hgen hindex published8 h18 J)
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
theorem c3HighAligned_degreeNine_ternaryPGroup_localRow_of_sufficient
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hgen : PrimitiveNormalGeneratorInput)
    (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    (h18 : DegreeEighteenTernaryHeadBound)
    (j : C3HighAlignedFirstOwnerIndex)
    (hkind : c3PhysicalOwnerKindEquiv j.1.2.1 =
      C3PhysicalOwnerKind.ternaryPGroup)
    (hwidth : c3HighAlignedFirstOwnerWidth j = 9) :
    C3HighAlignedLocalRow j := by
  obtain ⟨D, hD, h⟩ :=
    c3HighAligned_degreeNine_unrestricted_local_bound_of_sufficient
      hChief hgen hindex published8 h18 j hkind hwidth
  exact C3HighAlignedLocalRow.of_kernel j .degreeNine D hD h

end SymmetricSubgroupAsymptotics


/-! The old-owner refined cover and finite forward assembly retain their
original actions/types, with actual bounded old-owner facts installed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics
open Filter
open scoped BigOperators

/-- The complete high-C3 owner is covered by refined aligned cells.  The
selected nested carrier is kept until the width-three ternary alternative
has been excluded on it. -/
theorem c3PhysicalStructuralOwner_refinedAlignedCover_of_sufficient
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hgen : PrimitiveNormalGeneratorInput)
    (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    (h18 : DegreeEighteenTernaryHeadBound)
    (n : ℕ) (hn : 27 ≤ n)
    (G : Subgroup (Equiv.Perm (Fin n)))
    (hG : G ∈ C3PhysicalStructuralOwnerSet n) :
    ∃ j : C3HighRefinedAlignedIndex,
      G ∈ FusionWidthCanonicalFamily
        (c3HighAlignedFirstOwnerAction j.1)
        (c3HighAlignedFirstOwnerWidth_le_of_twentySeven_le n hn j.1)
        (c3HighAlignedFirstOwnerPredicate j.1
          (n - c3HighAlignedFirstOwnerWidth j.1)) := by
  obtain ⟨ownerEligible, hEligible⟩ :=
    c3PhysicalStructuralBranchMenu_cover_of_sufficient
      hChief hWeight hgen hindex published8 h18 hG.2.1
  obtain ⟨owner, howner⟩ := firstOwned_exists
    (c3PatternStructuralBranchMenu n) G
      ⟨ownerEligible, hEligible, hG.2.2⟩
  rcases howner.1.1 with ⟨b, e, H, hphysical, hfull, o, N, hN,
    hHigh, hEarlier, hk⟩
  let A := OrbitProfileFromOrbits.orbitImage (C3ComplementSource b H) o
  letI : MulAction.IsPretransitive A o.orbit :=
    orbitImage_pretransitive (C3ComplementSource b H) o
  letI : N.Normal := hN
  have hdegrees : Nat.card o.orbit = 3 ∨ Nat.card o.orbit = 4 ∨
      Nat.card o.orbit = 6 ∨ Nat.card o.orbit = 9 ∨
      Nat.card o.orbit = 12 ∨ Nat.card o.orbit = 27 :=
    ternaryHigh_earlierOwner_degree_menu_of_sufficient
      hChief hWeight hgen hindex published8 h18 N hHigh hEarlier
  obtain ⟨d, hd⟩ := C3HighWidthLabel.exists_of_degree_menu hdegrees
  have hdegree : b + 3 = n := by
    have hcard := Nat.card_congr e
    have hternary : Nat.card TernaryCyclic = 3 := by
      rw [Nat.card_congr RepeatedMarkerOwnerBound.ternaryFinEquiv,
        Nat.card_fin]
    rw [Nat.card_sum, hternary, Nat.card_fin, Nat.card_fin] at hcard
    omega
  subst n
  let C : C3HighNestedCarrier.Data H := ⟨o, N, hN, hHigh⟩
  have hordinary' : ¬ IsCriticalSubgroup (b + 3)
      (relabelSubgroup e (C3HighNestedCarrier.physicalSubgroup H)) := by
    rw [hphysical]
    exact hG.1
  have howner' : FirstOwned (c3PatternStructuralBranchMenu (b + 3)) owner
      (relabelSubgroup e (C3HighNestedCarrier.physicalSubgroup H)) := by
    rwa [hphysical]
  have hnon2 : ¬ IsPGroup 2 A := by
    exact strict_ternaryRelativeHead_not_isPGroup_two N hHigh
  obtain ⟨i, eO, himage⟩ := Non2TransitiveActionClass.orbit_cover
    (C3ComplementSource b H) o hd.symm hnon2
  have haligned : C3HighAlignedOwnerAction
      (c3PhysicalOwnerKindEquiv owner) i.representative :=
    C.alignedOwnerAction_of_chart H hd.symm hEarlier
      (c3PhysicalOwnerKindEquiv owner) hk i.representative eO himage
  let j0 : C3HighFirstOwnerIndex := ⟨d, owner, i⟩
  let j : C3HighAlignedFirstOwnerIndex := ⟨j0, by
    simpa only [j0, c3HighFirstOwnerAction] using haligned⟩
  have hexcluded : ¬ C3HighAlignedDegreeThreeTernary j := by
    rintro ⟨hwidth, hkind⟩
    have hwidth' : d.width = 3 := hwidth
    have horbit : Nat.card C.orbit.orbit = 3 := by
      change Nat.card o.orbit = 3
      rw [← hd]
      exact hwidth'
    have hkind' : c3PhysicalOwnerKindEquiv owner =
        C3PhysicalOwnerKind.ternaryPGroup := hkind
    have hP : IsPGroup 3 A := by
      have h := hk
      rw [hkind'] at h
      exact h
    have hpattern : C1DegreeNineSourcePattern
        (C3HighNestedCarrier.physicalSubgroup H) := by
      apply (c1DegreeNineSourcePattern_relabel_iff e _).mp
      rw [hphysical]
      exact hG.2.2
    exact C.not_degreeThree_ternaryPGroup_of_pattern H horbit hfull hpattern hP
  have hmem := C.mem_non2FirstOwnerCanonicalFamily_forAction
    c3PatternStructuralBranchMenu c3PatternStructuralBranchMenu_natural
      H hd.symm e hordinary' owner howner' i eO himage
  refine ⟨⟨j, hexcluded⟩, ?_⟩
  simpa only [j, j0, c3HighAlignedFirstOwnerAction,
    c3HighAlignedFirstOwnerWidth, c3HighAlignedFirstOwnerPredicate,
    c3HighFirstOwnerAction, c3HighFirstOwnerWidth,
    c3HighFirstOwnerPredicate, hphysical] using hmem

/-- Pointwise estimates for the refined cells assemble at the literal
deleted complement degree. -/
theorem c3PhysicalStructuralOwnerRatio_le_refinedForwardRow_of_sufficient
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hgen : PrimitiveNormalGeneratorInput)
    (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    (h18 : DegreeEighteenTernaryHeadBound)
    (f : C3HighRefinedAlignedIndex → ℕ → ℝ)
    (hlocal : ∀ (j : C3HighRefinedAlignedIndex) (n : ℕ)
      (hn : c3HighAlignedFirstOwnerWidth j.1 ≤ n),
      (Nat.card (FusionWidthCanonicalFamily
        (c3HighAlignedFirstOwnerAction j.1) hn
        (c3HighAlignedFirstOwnerPredicate j.1
          (n - c3HighAlignedFirstOwnerWidth j.1))) : ℝ) /
          exactBenchmark n ≤
        f j (n - c3HighAlignedFirstOwnerWidth j.1) *
          ordinarySubgroupRatio (n - c3HighAlignedFirstOwnerWidth j.1))
    (n : ℕ) (hn : 27 ≤ n) :
    c3PhysicalStructuralOwnerRatio n ≤
      ∑ b ∈ Finset.range n,
        fusionForwardRow c3HighRefinedWidth f n b *
          ordinarySubgroupRatio b := by
  let widthLe : ∀ j : C3HighRefinedAlignedIndex,
      c3HighRefinedWidth j ≤ n :=
    fun j => c3HighAlignedFirstOwnerWidth_le_of_twentySeven_le n hn j.1
  have hcard := fusionPhysicalUnion_card_le
    (C3PhysicalStructuralOwnerSet n)
    (fun j : C3HighRefinedAlignedIndex =>
      FusionWidthCanonicalFamily (c3HighAlignedFirstOwnerAction j.1) (widthLe j)
        (c3HighAlignedFirstOwnerPredicate j.1
          (n - c3HighAlignedFirstOwnerWidth j.1)))
    (c3PhysicalStructuralOwner_refinedAlignedCover_of_sufficient
      hChief hWeight hgen hindex published8 h18 n hn)
  have hcardR : (Nat.card (C3PhysicalStructuralOwnerSet n) : ℝ) ≤
      ∑ j : C3HighRefinedAlignedIndex,
        (Nat.card (FusionWidthCanonicalFamily
          (c3HighAlignedFirstOwnerAction j.1) (widthLe j)
          (c3HighAlignedFirstOwnerPredicate j.1
            (n - c3HighAlignedFirstOwnerWidth j.1))) : ℝ) := by
    exact_mod_cast hcard
  have hsum :
      ∑ j : C3HighRefinedAlignedIndex,
          (Nat.card (FusionWidthCanonicalFamily
            (c3HighAlignedFirstOwnerAction j.1) (widthLe j)
            (c3HighAlignedFirstOwnerPredicate j.1
              (n - c3HighAlignedFirstOwnerWidth j.1))) : ℝ) /
            exactBenchmark n ≤
        ∑ j : C3HighRefinedAlignedIndex,
          f j (n - c3HighRefinedWidth j) *
            ordinarySubgroupRatio (n - c3HighRefinedWidth j) := by
    apply Finset.sum_le_sum
    intro j _
    exact hlocal j n (widthLe j)
  have hrow := fusionForwardRow_weighted_sum
    c3HighRefinedWidth f c3HighRefinedWidth_pos
    ordinarySubgroupRatio n widthLe
  calc
    c3PhysicalStructuralOwnerRatio n ≤
        (∑ j : C3HighRefinedAlignedIndex,
          (Nat.card (FusionWidthCanonicalFamily
            (c3HighAlignedFirstOwnerAction j.1) (widthLe j)
            (c3HighAlignedFirstOwnerPredicate j.1
              (n - c3HighAlignedFirstOwnerWidth j.1))) : ℝ)) /
          exactBenchmark n :=
      div_le_div_of_nonneg_right hcardR (exactBenchmark_pos n).le
    _ = ∑ j : C3HighRefinedAlignedIndex,
        (Nat.card (FusionWidthCanonicalFamily
          (c3HighAlignedFirstOwnerAction j.1) (widthLe j)
          (c3HighAlignedFirstOwnerPredicate j.1
            (n - c3HighAlignedFirstOwnerWidth j.1))) : ℝ) /
          exactBenchmark n := Finset.sum_div _ _ _
    _ ≤ ∑ j : C3HighRefinedAlignedIndex,
        f j (n - c3HighRefinedWidth j) *
          ordinarySubgroupRatio (n - c3HighRefinedWidth j) := hsum
    _ = _ := hrow.symm

/-- Exponentially decaying estimates on the refined cells give the complete
high-C3 structural-owner continuation. -/
noncomputable def c3PhysicalStructuralOwner_refinedExponentialForwardEstimate_of_sufficient
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hgen : PrimitiveNormalGeneratorInput)
    (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    (h18 : DegreeEighteenTernaryHeadBound)
    (f : C3HighRefinedAlignedIndex → ℕ → ℝ)
    (hf : ∀ j b, 0 ≤ f j b)
    (hdecay : ∀ j, ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧
      ∀ᶠ b : ℕ in atTop, f j b ≤ C * (2 : ℝ) ^ (-κ * (b : ℝ)))
    (hlocal : ∀ (j : C3HighRefinedAlignedIndex) (n : ℕ)
      (hn : c3HighAlignedFirstOwnerWidth j.1 ≤ n),
      (Nat.card (FusionWidthCanonicalFamily
        (c3HighAlignedFirstOwnerAction j.1) hn
        (c3HighAlignedFirstOwnerPredicate j.1
          (n - c3HighAlignedFirstOwnerWidth j.1))) : ℝ) /
          exactBenchmark n ≤
        f j (n - c3HighAlignedFirstOwnerWidth j.1) *
          ordinarySubgroupRatio (n - c3HighAlignedFirstOwnerWidth j.1)) :
    OrdinaryFrontierClosure.ExponentialForwardEstimate
      c3PhysicalStructuralOwnerRatio := by
  let W := fusionForwardRow_decay c3HighRefinedWidth f
    c3HighRefinedWidth_pos hdecay
  let C : ℝ := Classical.choose W
  have hCκ := Classical.choose_spec W
  let κ : ℝ := Classical.choose hCκ
  have hspec := Classical.choose_spec hCκ
  let V := eventually_atTop.mp hspec.2.2
  let N : ℕ := Classical.choose V
  have hN := Classical.choose_spec V
  refine
    { scalar := fun _ => 0
      kernel := fusionForwardRow c3HighRefinedWidth f
      threshold := max 27 N
      rate := κ
      scalarConst := 1
      rowConst := C
      rate_pos := hspec.2.1
      scalarConst_pos := by norm_num
      rowConst_nonneg := hspec.1.le
      kernel_nonneg := ?_
      recurrence := ?_
      scalar_decay := ?_
      row_decay := ?_ }
  · intro n _ b _
    exact fusionForwardRow_nonneg c3HighRefinedWidth f hf n b
  · intro n hn
    have hn27 : 27 ≤ n := (le_max_left 27 N).trans hn
    exact (c3PhysicalStructuralOwnerRatio_le_refinedForwardRow_of_sufficient
      hChief hWeight hgen hindex published8 h18 f hlocal n hn27).trans_eq
        (zero_add _).symm
  · intro n _
    positivity
  · intro n hn
    exact hN n ((le_max_right 27 N).trans hn)

end SymmetricSubgroupAsymptotics

end


/-! Every old refined aligned cell keeps its exact local row, now using
proved local/actual head bounds. Its whole original physical owner sector
is exponentially contractive without a composition correspondence. -/
set_option autoImplicit false
noncomputable section
open Filter
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics
/-- Every aligned ternary p-group cell of width other than three has a local
row: its width is nine or twenty seven, and the positive-width ternary rows
apply. -/
theorem c3HighAligned_ternaryPGroup_localRow_of_sufficient
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hgen : PrimitiveNormalGeneratorInput)
    (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
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
      exact c3HighAligned_degreeNine_ternaryPGroup_localRow_of_sufficient hChief hgen hindex published8 h18
        ⟨⟨C3HighWidthLabel.nine, owner, i⟩, hj⟩ hk rfl
  | twentySeven =>
      exact c3HighAligned_degreeTwentySeven_ternaryPGroup_localRow
        ⟨⟨C3HighWidthLabel.twentySeven, owner, i⟩, hj⟩ hk rfl

/-- Exhaustion: every refined aligned cell reaches one of the ternary
p-group, natural-`A4`, degree-six, prime-base or binary-nine rows. -/
theorem c3HighRefinedAligned_localRow_of_sufficient
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hgen : PrimitiveNormalGeneratorInput)
    (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    (h18 : DegreeEighteenTernaryHeadBound)
    (hKP : KovacsPraegerAbelianizationBound)
    (j : C3HighRefinedAlignedIndex) :
    C3HighAlignedLocalRow j.1 := by
  obtain ⟨j, hj⟩ := j
  cases hk : c3PhysicalOwnerKindEquiv j.1.2.1 with
  | ternaryPGroup =>
      exact c3HighAligned_ternaryPGroup_localRow_of_sufficient hChief hgen hindex published8 h18 j hk
        (fun hw => hj ⟨hw, hk⟩)
  | naturalA4 => exact c3HighAligned_naturalA4_localRow j hk
  | degreeSix =>
      obtain ⟨D, hD, h⟩ := c3HighAligned_degreeSix_local_bound_of_sufficient hgen hindex published8 hKP j hk
      exact C3HighAlignedLocalRow.of_kernel j .degreeSix D hD h
  | degreeTwelve =>
      obtain ⟨r, D, hD, h⟩ :=
        c3HighAligned_degreeTwelve_local_bound_of_sufficient hChief hWeight hgen hindex published8 h18 j hk
      exact C3HighAlignedLocalRow.of_kernel j r D hD h

/-- The complete high-C3 structural-owner continuation, with no remaining
local-row hypothesis. -/
noncomputable def c3PhysicalStructuralOwner_closedExponentialForwardEstimate_of_sufficient
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hgen : PrimitiveNormalGeneratorInput)
    (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    (h18 : DegreeEighteenTernaryHeadBound)
    (hKP : KovacsPraegerAbelianizationBound) :
    OrdinaryFrontierClosure.ExponentialForwardEstimate
      c3PhysicalStructuralOwnerRatio :=
  let hrow := c3HighRefinedAligned_localRow_of_sufficient hChief hWeight hgen hindex published8 h18 hKP
  c3PhysicalStructuralOwner_refinedExponentialForwardEstimate_of_sufficient
    hChief hWeight hgen hindex published8 h18
    (fun j => Classical.choose (hrow j))
    (fun j => (Classical.choose_spec (hrow j)).1)
    (fun j => (Classical.choose_spec (hrow j)).2.1)
    (fun j => (Classical.choose_spec (hrow j)).2.2)

end SymmetricSubgroupAsymptotics
