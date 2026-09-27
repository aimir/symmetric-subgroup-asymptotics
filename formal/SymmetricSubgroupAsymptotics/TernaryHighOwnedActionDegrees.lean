import SymmetricSubgroupAsymptotics.TernaryDegreeTwentySevenReduction
import SymmetricSubgroupAsymptotics.TernaryHighActionDegrees

/-!
# Owner-aware high ternary action menu

The degree-nine row closes structurally through its three-by-three minimal
block system.  The degree-twenty-seven row then has a degree-three fibre over
that exact rank-two degree-nine top.  The same inversion dichotomy sends both
whole actions to the existing 3-group owner.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- Every high ternary pair is either already owned by the transitive
3-group branch or has one of the four genuinely bounded residual degrees. -/
theorem ternaryHigh_action_owned_menu
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    {A Ω : Type} [Group A] [Finite A] [Finite Ω] [MulAction A Ω]
    [FaithfulSMul A Ω] [MulAction.IsPretransitive A Ω]
    (N : Subgroup A) [N.Normal]
    (hHigh : 3 * Nat.card Ω <
      20 * Module.finrank (ZMod 3) (primeRelativeCharacters 3 N)) :
    IsPGroup 3 A ∨ Nat.card Ω = 3 ∨ Nat.card Ω = 4 ∨
      Nat.card Ω = 6 ∨ Nat.card Ω = 12 := by
  have hTwo : 2 ≤ Nat.card Ω := by
    by_contra h
    have hsmall : Nat.card Ω ≤ 1 := by omega
    letI : Subsingleton Ω := Finite.card_le_one_iff_subsingleton.mp hsmall
    have hz := primeRelativeHead_subsingleton_action (A := A) (Ω := Ω) 3 N
    omega
  letI : Nontrivial Ω := Finite.one_lt_card_iff_nontrivial.mp hTwo
  rcases ternaryHigh_action_rank_menu hChief hWeight hPrimitive h18 N hHigh with
    h3 | h4 | h6 | h9 | h12 | h27
  · exact Or.inr (Or.inl h3.1)
  · exact Or.inr (Or.inr (Or.inl h4.1))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h6.1)))
  · left
    exact degreeNine_rankTwo_isPGroup
      hChief hPrimitive h18 N h9.1 h9.2
  · exact Or.inr (Or.inr (Or.inr (Or.inr h12.1)))
  · left
    have himprimitive : ¬ MulAction.IsPreprimitive A Ω := by
      intro hp
      letI : MulAction.IsPreprimitive A Ω := hp
      have hSafe := hPrimitive A Ω (by omega) (by omega) (by omega) N
      omega
    exact highDegreeTwentySeven_imprimitive_isPGroup
      hChief hPrimitive h18 N himprimitive h27.1 hHigh

/-- The actual orbit witness carried by a high trivial-axis C3 state now
lands either in the existing 3-group owner or in one of four bounded action
degrees.  The original normal subgroup and strict high inequality are
retained. -/
theorem c3TrivialHigh_action_owned_menu
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    (b : ℕ)
    (P : Subgroup (ternaryRegularAction × Equiv.Perm (Fin b)) → Prop)
    (H : Subgroup (ternaryRegularAction × Equiv.Perm (Fin b)))
    (hH : C3TrivialHighPredicate b P H) :
    ∃ o : OrbitProfileFromOrbits.Orbit (C3ComplementSource b H),
      ∃ (N : Subgroup
          (OrbitProfileFromOrbits.orbitImage (C3ComplementSource b H) o))
        (hN : N.Normal),
        (3 * Nat.card o.orbit <
          20 * Module.finrank (ZMod 3) (primeRelativeCharacters 3 N)) ∧
        (IsPGroup 3
            (OrbitProfileFromOrbits.orbitImage (C3ComplementSource b H) o) ∨
          Nat.card o.orbit = 3 ∨ Nat.card o.orbit = 4 ∨
          Nat.card o.orbit = 6 ∨ Nat.card o.orbit = 12) := by
  obtain ⟨o, N, hN, hHigh⟩ := c3TrivialHigh_actualOrbit_witness b P H hH
  let A := OrbitProfileFromOrbits.orbitImage (C3ComplementSource b H) o
  letI : MulAction.IsPretransitive A o.orbit :=
    orbitImage_pretransitive (C3ComplementSource b H) o
  letI : N.Normal := hN
  refine ⟨o, N, hN, hHigh, ?_⟩
  exact ternaryHigh_action_owned_menu
    hChief hWeight hPrimitive h18 N hHigh

end SymmetricSubgroupAsymptotics

end
