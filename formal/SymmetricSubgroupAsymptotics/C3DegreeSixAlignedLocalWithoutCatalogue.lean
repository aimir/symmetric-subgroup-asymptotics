import SymmetricSubgroupAsymptotics.C3DegreeSixAlignedLocal
import SymmetricSubgroupAsymptotics.DegreeSixHighStructuralOwnerWithoutCatalogue

/-! The unchanged aligned six-point physical row consumes only the proved
actual six-point owner split. -/
set_option autoImplicit false
noncomputable section
open Filter
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics
theorem degreeSix_alignedAction_quotientConstants_without_catalogue
    (hgen : PrimitiveNormalGeneratorInput)
    (hindex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
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
  rcases degreeSix_high_oddIndexOwner_or_binaryBlock_without_catalogue hgen hindex published8 (A := U) (Ω := Fin 6)
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
theorem degreeSix_alignedAction_physical_owner_bound_without_catalogue
    (hgen : PrimitiveNormalGeneratorInput)
    (hindex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
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
    (degreeSix_alignedAction_quotientConstants_without_catalogue hgen hindex published8 hKP U hU)

/-- An aligned degree-six cell, whether its intrinsic owner is the
odd-index-two owner or the cyclic binary-module owner, satisfies the
degree-six row in the exact form consumed by the aligned continuation. -/
theorem c3HighAligned_degreeSix_local_bound_without_catalogue
    (hgen : PrimitiveNormalGeneratorInput)
    (hindex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
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
      obtain ⟨D, hD, hphys⟩ := degreeSix_alignedAction_physical_owner_bound_without_catalogue
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
