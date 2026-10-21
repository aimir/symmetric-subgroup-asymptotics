import SymmetricSubgroupAsymptotics.TernaryRelaxedStabilityArithmetic
import SymmetricSubgroupAsymptotics.PrimitiveTenTwelveHeadCapacity
import SymmetricSubgroupAsymptotics.PrimitiveTernaryStrictHeadAwayFromTenTwelve

/-! A complete actual-action stability theorem sufficient for the enlarged
high-orbit frontier. It relaxes degree10 to2 and retains every original
normal subgroup in the minimal-block induction. No strict-head premise or
primitive composition correspondence is introduced. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
open PrimitiveSocleRawStructure
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

theorem primitiveTernary_relaxed_stability_input_without_catalogue
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r/3))
    (hgen : PrimitiveNormalGeneratorInput) (hindex : PublishedSimpleIndexBounds)
    (published8 : DegreeEightCanonicalCatalogue.PublishedClassification) :
    PrimitiveTernaryHeadBoundOutside ternaryRelaxedStabilityBound ({18} : Finset ℕ) := by
  intro G X _ _ _ _ _ _ _ hF N _
  have h18 : Nat.card X≠18 := by simpa only [Finset.mem_singleton] using hF
  by_cases hsmall : Nat.card X=3 ∨ Nat.card X=4
  · obtain ⟨c,hc⟩ := hChief G X
    have hh := (primeRelativeHead_le_actualChiefWeight N c).trans hc
    rcases hsmall with h|h <;>
      simpa only [h,ternaryRelaxedStabilityBound,ternaryStabilityBound] using hh
  by_cases hex : Nat.card X=10 ∨ Nat.card X=12
  · cases Classical.choice (publishedONanScottStructure G X) with
    | inl D =>
        have hh := D.ten_twelve_relativeHead_le_two hindex hex N
        rcases hex with h|h <;>
          simpa only [h,ternaryRelaxedStabilityBound,ternaryStabilityBound] using hh
    | inr P =>
        have hs := P.small_ternaryRelativeHead_strict inferInstance (by omega)
          (by omega) (by omega) N
        have hh := ternaryStrictHead_le_stability_base _ _ hs
        exact hh.trans ((ternaryStability_base_le _ h18).trans
          (ternaryStability_le_relaxed _))
  have hs := primitiveTernaryStrictHead_awayFromTenTwelve_without_catalogue
    hgen hindex published8 G X (by omega) (by omega) (by omega) (by omega) N
  exact (ternaryStrictHead_le_stability_base _ _ hs).trans
    ((ternaryStability_base_le _ h18).trans (ternaryStability_le_relaxed _))

/-- Degree10 is the only changed value; degree12 already had head bound2. -/
theorem transitiveTernaryHead_relaxed_stability_without_catalogue
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r/3))
    (hgen : PrimitiveNormalGeneratorInput) (hindex : PublishedSimpleIndexBounds)
    (published8 : DegreeEightCanonicalCatalogue.PublishedClassification)
    (h18 : DegreeEighteenTernaryHeadBound)
    {A X : Type} [Group A] [Finite A] [Finite X] [MulAction A X]
    [FaithfulSMul A X] [MulAction.IsPretransitive A X] [Nonempty X]
    (N : Subgroup A) [N.Normal] :
    Module.finrank (ZMod 3) (primeRelativeCharacters 3 N)≤
      ternaryRelaxedStabilityBound (Nat.card X) := by
  apply transitiveTernaryHead_bound_with_finite_bypass
    ternaryRelaxedStabilityBound (fun r => r/3) ({18} : Finset ℕ) ?_
    (primitiveTernary_relaxed_stability_input_without_catalogue hChief hgen hindex published8)
    hChief ?_ N
  · intro G Y _ _ _ _ _ _ _ hY M _
    have hy : Nat.card Y=18 := by simpa only [Finset.mem_singleton] using hY
    simpa only [hy,ternaryRelaxedStabilityBound,ternaryStabilityBound] using h18 G Y hy M
  · intro r s hr hs hf
    exact ternaryRelaxedStability_scalar r s hr hs
      (by simpa only [Finset.mem_singleton] using hf)

end SymmetricSubgroupAsymptotics
