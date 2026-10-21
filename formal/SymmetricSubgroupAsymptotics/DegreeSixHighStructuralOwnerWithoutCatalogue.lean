import SymmetricSubgroupAsymptotics.DegreeSixBinaryBlockOwner
import SymmetricSubgroupAsymptotics.PrimitiveTernaryStrictHeadAwayFromTenTwelve

/-! The actual degree6 owner argument only needs its proved local primitive
strict bound, rather than a strict-head premise over every primitive action. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics

/-- Every high degree-six pair either already has the normal index-two
ternary owner, or its internally selected minimal block system is the sole
remaining two-by-three binary-block branch. -/
theorem degreeSix_high_oddIndexOwner_or_binaryBlock_without_catalogue
    (hgen : PrimitiveNormalGeneratorInput)
    (hindex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    {A Ω : Type} [Group A] [Finite A] [Finite Ω] [MulAction A Ω]
    [FaithfulSMul A Ω] [MulAction.IsPretransitive A Ω]
    (N : Subgroup A) [N.Normal]
    (hDegree : Nat.card Ω = 6)
    (hHigh : 3 * Nat.card Ω <
      20 * Module.finrank (ZMod 3) (primeRelativeCharacters 3 N)) :
    Nonempty (C1OddIndexTwoOwnerWitness A) ∨
      ∃ (ω₀ : Ω) (D : OriginalMinimalBlock (A := A) ω₀),
        Nat.card D.Fibre = 2 ∧ Nat.card D.Points = 3 := by
  have hΩtwo : 2 ≤ Nat.card Ω := by omega
  letI : Nontrivial Ω := Finite.one_lt_card_iff_nontrivial.mp hΩtwo
  have himprimitive : ¬ MulAction.IsPreprimitive A Ω := by
    intro hp
    letI : MulAction.IsPreprimitive A Ω := hp
    have hSafe := primitiveTernaryStrictHead_awayFromTenTwelve_without_catalogue
      hgen hindex published8 A Ω (by omega) (by omega) (by omega) (by omega) N
    omega
  let ω₀ : Ω := Classical.choice inferInstance
  let D : OriginalMinimalBlock (A := A) ω₀ :=
    Classical.choice (originalMinimalBlock_nonempty ω₀ himprimitive)
  let r := Nat.card D.Fibre
  let s := Nat.card D.Points
  have hr : 2 ≤ r := by simpa only [r] using D.degrees_ge_two.1
  have hs : 2 ≤ s := by simpa only [s] using D.degrees_ge_two.2
  have hrs : r * s = 6 := by
    have hproduct : r * s = Nat.card Ω := by
      simpa only [r, s] using D.degree_product
    exact hproduct.trans hDegree
  have hfactors : (r = 2 ∧ s = 3) ∨ (r = 3 ∧ s = 2) := by
    have hrdiv : r ∣ 6 := ⟨s, hrs.symm⟩
    have hrle : r ≤ 6 := Nat.le_of_dvd (by decide) hrdiv
    interval_cases r <;> norm_num at hrs ⊢ <;> omega
  rcases hfactors with hrs23 | hrs32
  · exact Or.inr ⟨ω₀, D, by simpa only [r] using hrs23.1,
      by simpa only [s] using hrs23.2⟩
  · exact Or.inl (D.degreeSix_ternaryBlock_owner N
      (by simpa only [r] using hrs32.1)
      (by simpa only [s] using hrs32.2) hHigh)

/-- Both intrinsic degree6 owners are retained on the same original group. -/
theorem degreeSix_high_structuralOwner_without_catalogue
    (hgen : PrimitiveNormalGeneratorInput)
    (hindex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    {A Ω : Type} [Group A] [Finite A] [Finite Ω] [MulAction A Ω]
    [FaithfulSMul A Ω] [MulAction.IsPretransitive A Ω]
    (N : Subgroup A) [N.Normal] (hDegree : Nat.card Ω=6)
    (hHigh : 3*Nat.card Ω<20*Module.finrank (ZMod 3) (primeRelativeCharacters 3 N)) :
    Nonempty (C1OddIndexTwoOwnerWitness A) ∨
      Nonempty (C1CyclicBinaryModuleOwnerWitness A) := by
  rcases degreeSix_high_oddIndexOwner_or_binaryBlock_without_catalogue
    hgen hindex published8 N hDegree hHigh with hOdd|⟨x,D,hF,hP⟩
  · exact Or.inl hOdd
  · exact Or.inr (D.degreeSix_binaryBlock_owner N hF hP hHigh)

end SymmetricSubgroupAsymptotics

end
