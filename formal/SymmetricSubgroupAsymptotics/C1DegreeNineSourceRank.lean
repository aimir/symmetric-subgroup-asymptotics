import SymmetricSubgroupAsymptotics.TernaryOneExceptionalOrbitRank
import SymmetricSubgroupAsymptotics.TernaryDegreeFourClosure
import SymmetricSubgroupAsymptotics.TransitiveTernaryStability
import SymmetricSubgroupAsymptotics.C3HighFiniteReduction

/-!
# The one-regular-orbit degree-nine source budget

This file records the precise source pattern left by the degree-nine mixed
owner.  There is one distinguished regular `C3` orbit and no orbit carrying
the natural `A4` action.  The orbitwise ternary stability theorem then gives
the exact global budget

`9 d₃(J) ≤ 2 b + 3`.

The distinguished orbit is literal: its action group is the restriction
image of the same original permutation subgroup.  In particular no cyclicity
is inferred from a transitive action on nine unrelated labels.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- A literal original orbit on which the restriction image is a transitive
three-group of degree three, hence the regular `C3` action. -/
def IsRegularC3Orbit {X : Type} (J : Subgroup (Equiv.Perm X))
    (o : OrbitProfileFromOrbits.Orbit J) : Prop :=
  Nat.card o.orbit = 3 ∧ IsPGroup 3 (OrbitProfileFromOrbits.orbitImage J o)

/-- The exact source pattern retained by the mixed degree-nine owner: one
regular `C3` orbit, and no natural `A4` orbit anywhere in the same source. -/
def C1DegreeNineSourcePattern {X : Type}
    (J : Subgroup (Equiv.Perm X)) : Prop :=
  ∃ exceptional : OrbitProfileFromOrbits.Orbit J,
    IsRegularC3Orbit J exceptional ∧
    (∀ o, IsRegularC3Orbit J o → o = exceptional) ∧
    (∀ o, ¬ IsNaturalA4Action
      (OrbitProfileFromOrbits.orbitImage J o) o.orbit)

/-- The local capacity behind the one-exceptional-orbit sum.  Degrees three
and four are resolved by their exact action classifications; degree nine
uses its sharp stability value two; all other degrees use the ordinary
stability envelope. -/
theorem c1DegreeNineSource_local_capacity
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
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
  have hstable : d ≤ ternaryStabilityBound w := by
    exact transitiveTernaryHead_stability hChief hPrimitive h18 N
  by_cases h3 : w = 3
  · have hd : d ≤ 1 := by
      simpa only [w, h3, ternaryStabilityBound_three] using hstable
    by_cases hd0 : d = 0
    · simp only [d, hd0, zero_mul]
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
    simp only [d, hd0, zero_mul]
    omega
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

/-- The exact source-pattern rank budget used by every quotient target of
the mixed degree-nine top. -/
theorem c1DegreeNineSource_ternaryCharacterRank
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b)))
    (hsource : C1DegreeNineSourcePattern J) :
    9 * Module.finrank (ZMod 3) (PrimeCharacters 3 J) ≤ 2 * b + 3 := by
  obtain ⟨exceptional, hexceptional, hunique, hnoA4⟩ := hsource
  simpa only [Nat.card_fin] using
    ternaryCharacterRank_oneExceptionalOrbit J exceptional
      (c1DegreeNineSource_local_capacity hChief hPrimitive h18 J exceptional
        hexceptional hunique hnoA4)

end SymmetricSubgroupAsymptotics

end
