import SymmetricSubgroupAsymptotics.C3HighFiniteReduction

/-!
# Necessary degrees for a high ternary relative pair

The primitive strict-head input leaves only degrees three, four and eighteen;
the all-action degree-eighteen bound removes the last of these.  The checked
minimal-block reduction handles the imprimitive case.  Thus every faithful
transitive pair above `3/20` has degree `3`, `4`, `6`, `9`, `12`, or `27`.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

theorem ternaryHigh_action_degree_menu
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    {A Ω : Type} [Group A] [Finite A] [Finite Ω] [MulAction A Ω]
    [FaithfulSMul A Ω] [MulAction.IsPretransitive A Ω]
    (N : Subgroup A) [N.Normal]
    (hhigh : 3 * Nat.card Ω <
      20 * Module.finrank (ZMod 3) (primeRelativeCharacters 3 N)) :
    Nat.card Ω = 3 ∨ Nat.card Ω = 4 ∨ Nat.card Ω = 6 ∨
      Nat.card Ω = 9 ∨ Nat.card Ω = 12 ∨ Nat.card Ω = 27 := by
  have hΩtwo : 2 ≤ Nat.card Ω := by
    by_contra h
    have hsmall : Nat.card Ω ≤ 1 := by omega
    letI : Subsingleton Ω := Finite.card_le_one_iff_subsingleton.mp hsmall
    have hz := primeRelativeHead_subsingleton_action (A := A) (Ω := Ω) 3 N
    omega
  letI : Nontrivial Ω := Finite.one_lt_card_iff_nontrivial.mp hΩtwo
  by_cases hp : MulAction.IsPreprimitive A Ω
  · letI : MulAction.IsPreprimitive A Ω := hp
    by_cases h3 : Nat.card Ω = 3
    · exact Or.inl h3
    by_cases h4 : Nat.card Ω = 4
    · exact Or.inr (Or.inl h4)
    by_cases h18degree : Nat.card Ω = 18
    · have hrank := h18 A Ω h18degree N
      omega
    · have hsafe := hPrimitive A Ω h3 h4 h18degree N
      omega
  · rcases ternaryHigh_imprimitive_degree_menu hChief hWeight hPrimitive h18
      N hp hhigh with h6 | h9 | h12 | h18degree | h27
    · exact Or.inr (Or.inr (Or.inl h6))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h9)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h12))))
    · have hrank := h18 A Ω h18degree N
      omega
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h27))))

/-- The stability envelope fixes the relative rank on every surviving
degree.  These are the exact normal-pair rows required from the bounded
action certificates. -/
theorem ternaryHigh_action_rank_menu
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    {A Ω : Type} [Group A] [Finite A] [Finite Ω] [MulAction A Ω]
    [FaithfulSMul A Ω] [MulAction.IsPretransitive A Ω]
    (N : Subgroup A) [N.Normal]
    (hhigh : 3 * Nat.card Ω <
      20 * Module.finrank (ZMod 3) (primeRelativeCharacters 3 N)) :
    (Nat.card Ω = 3 ∧
        Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) = 1) ∨
      (Nat.card Ω = 4 ∧
        Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) = 1) ∨
      (Nat.card Ω = 6 ∧
        Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) = 1) ∨
      (Nat.card Ω = 9 ∧
        Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) = 2) ∨
      (Nat.card Ω = 12 ∧
        Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) = 2) ∨
      (Nat.card Ω = 27 ∧
        Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) = 5) := by
  have hdegree := ternaryHigh_action_degree_menu hChief hWeight hPrimitive h18 N hhigh
  have hpositive : 0 < Nat.card Ω := by
    rcases hdegree with h3 | h4 | h6 | h9 | h12 | h27 <;> omega
  letI : Nonempty Ω := (Nat.card_pos_iff.mp hpositive).1
  have htop := transitiveTernaryHead_stability hChief hPrimitive h18
    (A := A) (Ω := Ω) N
  rcases hdegree with h3 | h4 | h6 | h9 | h12 | h27
  · left
    refine ⟨h3, ?_⟩
    simp only [h3, ternaryStabilityBound_three] at htop hhigh
    omega
  · exact Or.inr (Or.inl ⟨h4, by
      simp only [h4, ternaryStabilityBound_four] at htop hhigh
      omega⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨h6, by
      norm_num [h6, ternaryStabilityBound] at htop hhigh
      omega⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h9, by
      simp only [h9, ternaryStabilityBound_nine] at htop hhigh
      omega⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h12, by
      norm_num [h12, ternaryStabilityBound] at htop hhigh
      omega⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h27, by
      norm_num [h27, ternaryStabilityBound] at htop hhigh
      omega⟩))))

/-- The sole high C3 branch therefore exposes a normal pair in a literal
original orbit action of one of the six necessary degrees. -/
theorem c3TrivialHigh_action_degree_menu
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
        (Nat.card o.orbit = 3 ∨ Nat.card o.orbit = 4 ∨
          Nat.card o.orbit = 6 ∨ Nat.card o.orbit = 9 ∨
          Nat.card o.orbit = 12 ∨ Nat.card o.orbit = 27) := by
  obtain ⟨o, N, hN, hhigh⟩ := c3TrivialHigh_actualOrbit_witness b P H hH
  let A := OrbitProfileFromOrbits.orbitImage (C3ComplementSource b H) o
  letI : MulAction.IsPretransitive A o.orbit :=
    orbitImage_pretransitive (C3ComplementSource b H) o
  letI : N.Normal := hN
  refine ⟨o, N, hN, hhigh, ?_⟩
  have hhigh' : 3 * Nat.card o.orbit <
      20 * Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) := by
    simpa only using hhigh
  exact ternaryHigh_action_degree_menu hChief hWeight hPrimitive h18 N hhigh'

/-- Exact degree/rank normal-pair witness supplied by a high C3 state. -/
theorem c3TrivialHigh_action_rank_menu
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
        ((Nat.card o.orbit = 3 ∧
            Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) = 1) ∨
          (Nat.card o.orbit = 4 ∧
            Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) = 1) ∨
          (Nat.card o.orbit = 6 ∧
            Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) = 1) ∨
          (Nat.card o.orbit = 9 ∧
            Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) = 2) ∨
          (Nat.card o.orbit = 12 ∧
            Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) = 2) ∨
          (Nat.card o.orbit = 27 ∧
            Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) = 5)) := by
  obtain ⟨o, N, hN, hhigh⟩ := c3TrivialHigh_actualOrbit_witness b P H hH
  let A := OrbitProfileFromOrbits.orbitImage (C3ComplementSource b H) o
  letI : MulAction.IsPretransitive A o.orbit :=
    orbitImage_pretransitive (C3ComplementSource b H) o
  letI : N.Normal := hN
  refine ⟨o, N, hN, hhigh, ?_⟩
  have hhigh' : 3 * Nat.card o.orbit <
      20 * Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) := by
    simpa only using hhigh
  exact ternaryHigh_action_rank_menu hChief hWeight hPrimitive h18 N hhigh'

end SymmetricSubgroupAsymptotics

end
