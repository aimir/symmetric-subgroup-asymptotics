import SymmetricSubgroupAsymptotics.C1DegreeNineSourceRank

/-!
# Ternary rank after all small exceptional orbits are removed

The degree-three regular `C3` action and the degree-four natural `A4`
action are the two small exceptions to the ordinary ternary stability
budget.  Once neither occurs as an actual orbit image, the literal orbit
filtration gives the uniform global estimate

`9 d₃(J) ≤ 2 |X|`.

This is the rank input used by the repeated-`C3` packet: all regular triples
are extracted into the elementary top, leaving precisely such a tail.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- No actual orbit image is one of the two small ternary exceptions. -/
def NoRegularC3OrNaturalA4Orbits {X : Type}
    (J : Subgroup (Equiv.Perm X)) : Prop :=
  ∀ o : OrbitProfileFromOrbits.Orbit J,
    ¬ IsRegularC3Orbit J o ∧
      ¬ IsNaturalA4Action (OrbitProfileFromOrbits.orbitImage J o) o.orbit

/-- The local relative-head estimate on a nonexceptional literal orbit. -/
theorem ternaryNoSmallOrbit_local_capacity
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    {X : Type} [Finite X] (J : Subgroup (Equiv.Perm X))
    (hsmall : NoRegularC3OrNaturalA4Orbits J)
    (o : OrbitProfileFromOrbits.Orbit J)
    (N : Subgroup (OrbitProfileFromOrbits.orbitImage J o)) (hN : N.Normal) :
    letI := hN
    9 * Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) ≤
      2 * Nat.card o.orbit := by
  let A := OrbitProfileFromOrbits.orbitImage J o
  let w := Nat.card o.orbit
  let d := Module.finrank (ZMod 3) (primeRelativeCharacters 3 N)
  letI : MulAction.IsPretransitive A o.orbit := orbitImage_pretransitive J o
  letI : Nonempty o.orbit := ⟨⟨o.out, by
    rw [o.orbit_eq_orbit_out Quotient.out_eq']
    exact MulAction.mem_orbit_self o.out⟩⟩
  letI : N.Normal := hN
  have hstable : d ≤ ternaryStabilityBound w := by
    exact transitiveTernaryHead_stability hChief hPrimitive h18 N
  by_cases h3 : w = 3
  · have hd : d ≤ 1 := by
      simpa only [w, h3, ternaryStabilityBound_three] using hstable
    have hd0 : d = 0 := by
      by_contra hd0
      have hd1 : d = 1 := by omega
      exact (hsmall o).1 ⟨h3, degreeThree_rankOne_isPGroup h3 N hd1⟩
    simp [d, hd0]
  by_cases h4 : w = 4
  · have hd : d ≤ 1 := by
      simpa only [w, h4, ternaryStabilityBound_four] using hstable
    have hd0 : d = 0 := by
      by_contra hd0
      have hd1 : d = 1 := by omega
      exact (hsmall o).2 (degreeFour_rankOne_isNaturalA4 h4 N hd1)
    simp [d, hd0]
  by_cases h9 : w = 9
  · have hd : d ≤ 2 := by
      simpa only [w, h9, ternaryStabilityBound_nine] using hstable
    omega
  · have hord : d ≤ 5 * w / 27 :=
      transitiveTernaryHead_stability_ordinary hChief hPrimitive h18 N h3 h4 h9
    have hmul : 27 * d ≤ 5 * w :=
      by simpa only [Nat.mul_comm] using
        (Nat.le_div_iff_mul_le (by decide : 0 < 27)).mp hord
    omega

/-- Removing every regular `C3` orbit and every natural `A4` orbit improves
the permutation ternary-character rank from `|X|/3` to `2|X|/9`. -/
theorem ternaryCharacterRank_noSmallOrbits
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    {X : Type} [Finite X] (J : Subgroup (Equiv.Perm X))
    (hsmall : NoRegularC3OrNaturalA4Orbits J) :
    9 * Module.finrank (ZMod 3) (PrimeCharacters 3 J) ≤ 2 * Nat.card X := by
  exact primeCharacterRank_actualOrbit_cap 3 J 2 9 (by omega)
    (ternaryNoSmallOrbit_local_capacity hChief hPrimitive h18 J hsmall)

end SymmetricSubgroupAsymptotics

end
