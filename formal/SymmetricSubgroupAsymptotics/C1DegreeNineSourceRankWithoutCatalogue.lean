import SymmetricSubgroupAsymptotics.C1DegreeNineSourceRank
import SymmetricSubgroupAsymptotics.TransitiveTernaryRelaxedStabilityWithoutCatalogue

/-! The original orbitwise source rank budgets tolerate head2 at degree10:
9*2≤2*10. No old strict-head premise is needed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics
/-- The local capacity behind the one-exceptional-orbit sum.  Degrees three
and four are resolved by their exact action classifications; degree nine
uses its sharp stability value two; all other degrees use the ordinary
stability envelope. -/
theorem c1DegreeNineSource_local_capacity_without_catalogue
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hgen : PrimitiveNormalGeneratorInput)
    (hindex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    (h18 : DegreeEighteenTernaryHeadBound)
    {X : Type} [Finite X] (J : Subgroup (Equiv.Perm X))
    (exceptional : OrbitProfileFromOrbits.Orbit J)
    (hexceptional : IsRegularC3Orbit J exceptional)
    (hunique : ∀ o, IsRegularC3Orbit J o → o = exceptional)
    (hnoA4 : ∀ o, ¬ IsNaturalA4Action
      (OrbitProfileFromOrbits.orbitImage J o) o.orbit)
    (o : OrbitProfileFromOrbits.Orbit J)
    (N : Subgroup (OrbitProfileFromOrbits.orbitImage J o)) (hN : N.Normal) :
    letI := hN
    9 * Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) ≤
      2 * Nat.card o.orbit + if o = exceptional then 3 else 0 := by
  let A := OrbitProfileFromOrbits.orbitImage J o
  let w := Nat.card o.orbit
  let d := Module.finrank (ZMod 3) (primeRelativeCharacters 3 N)
  letI : MulAction.IsPretransitive A o.orbit := orbitImage_pretransitive J o
  letI : Nonempty o.orbit := ⟨⟨o.out, by
    rw [o.orbit_eq_orbit_out Quotient.out_eq']
    exact MulAction.mem_orbit_self o.out⟩⟩
  letI : N.Normal := hN
  have hrel : d≤ternaryRelaxedStabilityBound w := by
    exact transitiveTernaryHead_relaxed_stability_without_catalogue
      hChief hgen hindex published8 h18 N
  by_cases h10 : w=10
  · have hd : d≤2 := by simpa only [h10,ternaryRelaxedStabilityBound] using hrel
    omega
  have hstable : d≤ternaryStabilityBound w := by
    simpa only [ternaryRelaxedStabilityBound,if_neg h10] using hrel
  by_cases h3 : w = 3
  · have hd : d ≤ 1 := by
      simpa only [w, h3, ternaryStabilityBound_three] using hstable
    by_cases hd0 : d = 0
    · simp only [d, hd0]
      omega
    · have hd1 : d = 1 := by omega
      have hgroup : IsPGroup 3 A :=
        degreeThree_rankOne_isPGroup h3 N hd1
      have hoe : o = exceptional := hunique o ⟨h3, hgroup⟩
      have hcard : Nat.card exceptional.orbit = 3 := by
        rw [← hoe]
        exact h3
      simp only [d, hd1, hoe, ↓reduceIte]
      omega
  by_cases h4 : w = 4
  · have hd : d ≤ 1 := by
      simpa only [w, h4, ternaryStabilityBound_four] using hstable
    have hd0 : d = 0 := by
      by_contra hd0
      have hd1 : d = 1 := by omega
      exact hnoA4 o (degreeFour_rankOne_isNaturalA4 h4 N hd1)
    simp only [d, hd0]
    omega
  by_cases h9 : w = 9
  · have hd : d ≤ 2 := by
      simpa only [w, h9, ternaryStabilityBound_nine] using hstable
    omega
  · have hord : d ≤ 5 * w / 27 :=
      hstable.trans (ternaryStability_le_base w h3 h4 h9)
    have hmul : 27 * d ≤ 5 * w :=
      by simpa only [Nat.mul_comm] using
        (Nat.le_div_iff_mul_le (by decide : 0 < 27)).mp hord
    omega

/-- The exact source-pattern rank budget used by every quotient target of
the mixed degree-nine top. -/
theorem c1DegreeNineSource_ternaryCharacterRank_without_catalogue
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hgen : PrimitiveNormalGeneratorInput)
    (hindex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    (h18 : DegreeEighteenTernaryHeadBound)
    {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b)))
    (hsource : C1DegreeNineSourcePattern J) :
    9 * Module.finrank (ZMod 3) (PrimeCharacters 3 J) ≤ 2 * b + 3 := by
  obtain ⟨exceptional, hexceptional, hunique, hnoA4⟩ := hsource
  simpa only [Nat.card_fin] using
    ternaryCharacterRank_oneExceptionalOrbit J exceptional
      (c1DegreeNineSource_local_capacity_without_catalogue hChief hgen hindex published8 h18 J exceptional
        hexceptional hunique hnoA4)

end SymmetricSubgroupAsymptotics

end
