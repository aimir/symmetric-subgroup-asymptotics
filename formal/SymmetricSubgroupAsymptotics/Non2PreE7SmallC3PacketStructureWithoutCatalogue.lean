import SymmetricSubgroupAsymptotics.Non2PreE7SmallC3PacketStructure
import SymmetricSubgroupAsymptotics.TernaryRelaxedHighActionDegrees

/-! Actual-consumer adapter without the composition catalogue. The original
physical families, rank caps, normal axes and numerical kernels are retained. -/
set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
open RepeatedC3TailPhysical RepeatedC3TailExtraction

private theorem tailOrbit_card_eq_ambient
    {n : ℕ} (G : Subgroup (Equiv.Perm (Fin n)))
    (q : OrbitProfileFromOrbits.Orbit (tailImage G)) :
    Nat.card q.orbit = Nat.card (ambientOrbit G q).1.orbit :=
  Nat.card_congr (orbitEquiv G q)

private theorem tailOrbit_not_twoGroup_of_high
    {n : ℕ} (G : Subgroup (Equiv.Perm (Fin n)))
    (q : OrbitProfileFromOrbits.Orbit (tailImage G))
    (N : Subgroup (OrbitProfileFromOrbits.orbitImage (tailImage G) q))
    [N.Normal]
    (hhigh : 3 * Nat.card q.orbit <
      20 * Module.finrank (ZMod 3) (primeRelativeCharacters 3 N)) :
    ¬ IsPGroup 2
      (OrbitProfileFromOrbits.orbitImage G (ambientOrbit G q).1) := by
  have htail : ¬ IsPGroup 2
      (OrbitProfileFromOrbits.orbitImage (tailImage G) q) :=
    strict_ternaryRelativeHead_not_isPGroup_two N hhigh
  intro hambient
  let e := orbitEquiv G q
  let A := OrbitProfileFromOrbits.orbitImage (tailImage G) q
  let B := OrbitProfileFromOrbits.orbitImage G (ambientOrbit G q).1
  have himage : relabelSubgroup e A = B := relabel_orbitImage G q
  let g : A ≃* B :=
    (e.permCongrHom.subgroupMap A).trans (MulEquiv.subgroupCongr himage)
  exact htail (hambient.of_equiv g.symm)

private theorem tailHigh_large_isViolation
    {n : ℕ} (G : Subgroup (Equiv.Perm (Fin n)))
    (q : OrbitProfileFromOrbits.Orbit (tailImage G))
    (N : Subgroup (OrbitProfileFromOrbits.orbitImage (tailImage G) q))
    [N.Normal]
    (hhigh : 3 * Nat.card q.orbit <
      20 * Module.finrank (ZMod 3) (primeRelativeCharacters 3 N))
    (hne : Nat.card q.orbit ≠ 3)
    (hle : Nat.card q.orbit ≤ 27) :
    IsPreE7ViolationOrbit G (ambientOrbit G q).1 := by
  refine ⟨tailOrbit_not_twoGroup_of_high G q N hhigh, ?_, ?_⟩
  · rintro ⟨e, _⟩
    have hcard := Nat.card_congr e
    have heq := tailOrbit_card_eq_ambient G q
    simp only [Nat.card_fin] at hcard
    omega
  · rintro ⟨d, hd, _, _⟩
    have hge := PairCountLabel.pairCount_ge_24 d
    have heq := tailOrbit_card_eq_ambient G q
    unfold PairCountLabel.sourceDegree at hd
    omega

/-- Every normal pair in the retained tail obeys the sharp `3/20`
capacity.  The proof uses the checked finite high-action degree menu and the
literal definition of the pre-E7 violation predicate. -/
theorem repeatedC3Tail_local_threeTwentieths_without_catalogue
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hgen : PrimitiveNormalGeneratorInput)
    (hindex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    (h18 : DegreeEighteenTernaryHeadBound)
    {n : ℕ} (G : Subgroup (Equiv.Perm (Fin n)))
    (hpacket : AllPreE7ViolationOrbitsDegreeThree G)
    (q : OrbitProfileFromOrbits.Orbit (tailImage G))
    (N : Subgroup (OrbitProfileFromOrbits.orbitImage (tailImage G) q))
    (hN : N.Normal) :
    letI := hN
    20 * Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) ≤
      3 * Nat.card q.orbit := by
  letI : N.Normal := hN
  letI : MulAction.IsPretransitive
      (OrbitProfileFromOrbits.orbitImage (tailImage G) q) q.orbit :=
    orbitImage_pretransitive (tailImage G) q
  letI : Nonempty q.orbit := ⟨⟨q.out, by
    rw [q.orbit_eq_orbit_out Quotient.out_eq']
    exact MulAction.mem_orbit_self q.out⟩⟩
  by_contra hcap
  have hhigh : 3 * Nat.card q.orbit <
      20 * Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) := by
    omega
  have hmenu := ternaryHigh_action_degree_menu_without_catalogue
    hChief hWeight hgen hindex published8 h18 N hhigh
  rcases hmenu with h3 | h4 | h6 | h9 | h10 | h12 | h27
  · have hp : IsPGroup 3
        (OrbitProfileFromOrbits.orbitImage (tailImage G) q) :=
      degreeThree_rankOne_isPGroup h3 N (by
        have ht := transitiveTernaryHead_relaxed_stability_without_catalogue
          hChief hgen hindex published8 h18 (X := q.orbit) N
        have ht3 : Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) ≤ 1 := by
          simpa only [h3, ternaryRelaxedStabilityBound,
            if_neg (by decide : (3 : ℕ) ≠ 10), ternaryStabilityBound_three] using ht
        omega)
    have hp' := hp.map (orbitEquiv G q).permCongrHom.toMonoidHom
    change IsPGroup 3
      (relabelSubgroup (orbitEquiv G q)
        (OrbitProfileFromOrbits.orbitImage (tailImage G) q)) at hp'
    rw [relabel_orbitImage G q] at hp'
    exact (ambientOrbit G q).2 ⟨by
      rw [← tailOrbit_card_eq_ambient G q]
      exact h3, hp'⟩
  · have hbad := tailHigh_large_isViolation G q N hhigh (by omega) (by omega)
    have hdegree := hpacket (ambientOrbit G q).1 hbad
    rw [← tailOrbit_card_eq_ambient G q] at hdegree
    omega
  · have hbad := tailHigh_large_isViolation G q N hhigh (by omega) (by omega)
    have hdegree := hpacket (ambientOrbit G q).1 hbad
    rw [← tailOrbit_card_eq_ambient G q] at hdegree
    omega
  · have hbad := tailHigh_large_isViolation G q N hhigh (by omega) (by omega)
    have hdegree := hpacket (ambientOrbit G q).1 hbad
    rw [← tailOrbit_card_eq_ambient G q] at hdegree
    omega
  · have hbad := tailHigh_large_isViolation G q N hhigh (by omega) (by omega)
    have hdegree := hpacket (ambientOrbit G q).1 hbad
    rw [← tailOrbit_card_eq_ambient G q] at hdegree
    omega
  · have hbad := tailHigh_large_isViolation G q N hhigh (by omega) (by omega)
    have hdegree := hpacket (ambientOrbit G q).1 hbad
    rw [← tailOrbit_card_eq_ambient G q] at hdegree
    omega
  · have hbad := tailHigh_large_isViolation G q N hhigh (by omega) (by omega)
    have hdegree := hpacket (ambientOrbit G q).1 hbad
    rw [← tailOrbit_card_eq_ambient G q] at hdegree
    omega

/-- The complete original physical subgroup therefore enters the simultaneous
repeated-`C3` model with the `3/20` tail cap. -/
noncomputable def repeatedC3Tail_packetAssembly_without_catalogue
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hgen : PrimitiveNormalGeneratorInput)
    (hindex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    (h18 : DegreeEighteenTernaryHeadBound)
    {n : ℕ} (G : Subgroup (Equiv.Perm (Fin n)))
    (hpacket : AllPreE7ViolationOrbitsDegreeThree G) :
    AssembledOrbitProfileOn
      (RepeatedC3TailProfile.modelPredicate (regularCount G)
        (3 * tailDegree G / 20) (tailDegree G)) (Fin n) :=
  assembled_threeTwentieths G
    (repeatedC3Tail_local_threeTwentieths_without_catalogue
      hChief hWeight hgen hindex published8 h18 G hpacket)

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics
end
