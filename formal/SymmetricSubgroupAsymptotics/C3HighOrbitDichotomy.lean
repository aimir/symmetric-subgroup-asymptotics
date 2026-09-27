import SymmetricSubgroupAsymptotics.C3PhysicalFrontier
import SymmetricSubgroupAsymptotics.PrimePermutationOrbitFiltration

/-!
# The high trivial-axis C3 branch exposes an actual high orbit pair

The complement of a high trivial-axis state is the same literal subgroup
of the original symmetric group that occurs in the physical C3 chart.
Applying the all-orbit filtration to that subgroup produces a literal orbit
image and a literal normal subgroup with relative head above `3/20`.

Consequently an exhaustive local dichotomy--an earlier owner accepts the
pair, or the pair has `3/20` capacity--forces every high state into an
earlier owner.  This is the classification-facing interface; it contains
no assumption that the normal pair is abelian or a direct factor.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

abbrev C3ComplementSource (b : ℕ)
    (H : Subgroup (ternaryRegularAction × Equiv.Perm (Fin b))) :
    Subgroup (Equiv.Perm (Fin b)) :=
  H.map (MonoidHom.snd ternaryRegularAction (Equiv.Perm (Fin b)))

/-- Every state in the sole unresolved C3 branch supplies an actual
transitive orbit image and a normal pair above the relative `3/20` line. -/
theorem c3TrivialHigh_actualOrbit_witness (b : ℕ)
    (P : Subgroup (ternaryRegularAction × Equiv.Perm (Fin b)) → Prop)
    (H : Subgroup (ternaryRegularAction × Equiv.Perm (Fin b)))
    (hH : C3TrivialHighPredicate b P H) :
    ∃ o : OrbitProfileFromOrbits.Orbit (C3ComplementSource b H),
      ∃ (N : Subgroup
          (OrbitProfileFromOrbits.orbitImage (C3ComplementSource b H) o))
        (hN : N.Normal),
        letI := hN
        3 * Nat.card o.orbit <
          20 * Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) := by
  apply primeCharacterRank_actualOrbit_high 3 (C3ComplementSource b H) 3 20
    (by omega)
  simpa only [Nat.card_fin, ternaryCharacterRank] using hH.2.2

/-- If every actual orbit pair is either already owned or below the local
capacity line, a high C3 state necessarily supplies an owned pair. -/
theorem c3TrivialHigh_enters_orbitPairOwner (b : ℕ)
    (P : Subgroup (ternaryRegularAction × Equiv.Perm (Fin b)) → Prop)
    (H : Subgroup (ternaryRegularAction × Equiv.Perm (Fin b)))
    (Owner : ∀ o : OrbitProfileFromOrbits.Orbit (C3ComplementSource b H),
      ∀ N : Subgroup
        (OrbitProfileFromOrbits.orbitImage (C3ComplementSource b H) o),
        N.Normal → Prop)
    (hdichotomy : ∀ (o : OrbitProfileFromOrbits.Orbit (C3ComplementSource b H))
      (N : Subgroup
        (OrbitProfileFromOrbits.orbitImage (C3ComplementSource b H) o))
      (hN : N.Normal),
        letI := hN
        Owner o N hN ∨
          20 * Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) ≤
            3 * Nat.card o.orbit)
    (hH : C3TrivialHighPredicate b P H) :
    ∃ o : OrbitProfileFromOrbits.Orbit (C3ComplementSource b H),
      ∃ (N : Subgroup
          (OrbitProfileFromOrbits.orbitImage (C3ComplementSource b H) o))
        (hN : N.Normal), Owner o N hN := by
  obtain ⟨o, N, hN, hhigh⟩ := c3TrivialHigh_actualOrbit_witness b P H hH
  rcases hdichotomy o N hN with howned | hcap
  · exact ⟨o, N, hN, howned⟩
  · exact False.elim ((Nat.not_lt_of_ge hcap) hhigh)

/-- The owner-free specialization: uniform local capacity makes the high
trivial-axis branch empty. -/
theorem not_c3TrivialHigh_of_actualOrbit_caps (b : ℕ)
    (P : Subgroup (ternaryRegularAction × Equiv.Perm (Fin b)) → Prop)
    (H : Subgroup (ternaryRegularAction × Equiv.Perm (Fin b)))
    (hcap : ∀ (o : OrbitProfileFromOrbits.Orbit (C3ComplementSource b H))
      (N : Subgroup
        (OrbitProfileFromOrbits.orbitImage (C3ComplementSource b H) o))
      (hN : N.Normal),
        letI := hN
        20 * Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) ≤
          3 * Nat.card o.orbit) :
    ¬ C3TrivialHighPredicate b P H := by
  intro hH
  obtain ⟨o, N, hN, hhigh⟩ := c3TrivialHigh_actualOrbit_witness b P H hH
  exact (Nat.not_lt_of_ge (hcap o N hN)) hhigh

end SymmetricSubgroupAsymptotics

end
