import SymmetricSubgroupAsymptotics.CFSGSolubleOrbitCompression
import SymmetricSubgroupAsymptotics.CFSGSolubleOrbitNumerics

/-! Ordinary generation by weighted induction on the actual orbit list. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.CFSGSolubleOrbitConsequences
open MarkedC4 LargeOrbitGeneratorConsequences

noncomputable def orbitWeight (n : ℕ) : ℝ :=
  (n : ℝ) / Real.sqrt (Real.logb 2 n)

@[simp] theorem orbitWeight_one : orbitWeight 1 = 0 := by simp [orbitWeight]

theorem orbitWeight_nonneg (n : ℕ) : 0 ≤ orbitWeight n :=
  div_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)

/-- The correlated source, rather than a product of independently generated
orbit images, satisfies the sum of the transitive orbit costs. -/
theorem weighted_generator_bound
    (hTracey : TraceyRefinedInducedModuleInput)
    (S : ActionShape) (G : Type) [Group G] [Finite G] [IsSolvable G]
    (f : G →* S.Coordinates) (hf : Function.Injective f)
    (hp : ActionShape.TransitiveProfile f) :
    (genRank G : ℝ) ≤ 1280 * S.weight orbitWeight := by
  suffices h : ∀ n : ℕ, ∀ (T : ActionShape) (A : Type)
      [Group A] [Finite A] [IsSolvable A]
      (g : A →* T.Coordinates), Function.Injective g →
      ActionShape.TransitiveProfile g → T.degree = n →
      (genRank A : ℝ) ≤ 1280 * T.weight orbitWeight by
    exact h S.degree S G f hf hp rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro T A _ _ _ g hg hprofile hdegree
    cases T with
    | nil =>
      letI : Subsingleton A := ActionShape.subsingleton_of_nil g hg
      have hz : genRank A ≤ 0 := by
        simpa using (genRank_le (s := (∅ : Finset A))
          (Subsingleton.elim _ _))
      have hzR : (genRank A : ℝ) ≤ 0 := by exact_mod_cast hz
      simpa [ActionShape.weight] using hzR
    | @cons X fintypeX nonemptyX tail =>
      have hpos : 0 < Fintype.card X := Fintype.card_pos
      have htailLt : tail.degree < n := by
        change Fintype.card X + tail.degree = n at hdegree
        omega
      by_cases hsmall : Subsingleton X
      · letI : Subsingleton X := hsmall
        have ht := ih tail.degree htailLt tail A (ActionShape.tail g)
          (ActionShape.tail_injective_of_subsingleton g hg) hprofile.2 rfl
        have hcard : Fintype.card X = 1 := Fintype.card_eq_one_iff.mpr
          ⟨Classical.choice (inferInstance : Nonempty X), fun y => Subsingleton.elim _ _⟩
        simpa only [ActionShape.weight, hcard, orbitWeight_one, zero_add] using ht
      · letI : Nontrivial X := not_subsingleton_iff_nontrivial.mp hsmall
        have hr : 2 ≤ Fintype.card X := by
          have h := Fintype.one_lt_card_iff_nontrivial.mpr (inferInstance : Nontrivial X)
          omega
        letI : MulAction A X := MulAction.compHom X (ActionShape.head g)
        by_cases hprim : MulAction.IsPreprimitive A X
        · let q := ActionShape.tail g
          let Q := q.range
          letI : IsSolvable Q := solvable_of_surjective
            (f := q.rangeRestrict) q.rangeRestrict_surjective
          have hQprofile : ActionShape.TransitiveProfile q.range.subtype := by
            apply ActionShape.profile_of_comp q.range.subtype q.rangeRestrict
            change ActionShape.TransitiveProfile q
            exact hprofile.2
          have hQ := ih tail.degree htailLt tail Q q.range.subtype
            Subtype.val_injective hQprofile rfl
          have hstep := primitive_head_generator_bound g hg hprim hr
          have hstepR := hstep
          have hcost := CFSGSolubleOrbitNumerics.primitive_recurrence
            (Fintype.card X) hr
          change (genRank A : ℝ) ≤
            1280 * (orbitWeight (Fintype.card X) + tail.weight orbitWeight)
          have hcost' : (Real.logb 2 (Fintype.card X))^2 + Real.logb 2 (Fintype.card X) ≤
              1280 * orbitWeight (Fintype.card X) := by
            simpa only [orbitWeight, mul_div_assoc] using hcost
          nlinarith
        · obtain ⟨C⟩ := headCompression_nonempty hTracey g hg hprofile hprim hr
          have hnewLt : (ActionShape.cons C.Y tail).degree < n := by
            change Fintype.card X + tail.degree = n at hdegree
            change Fintype.card C.Y + tail.degree < n
            have := C.top_lt
            omega
          have hQ := ih (ActionShape.cons C.Y tail).degree hnewLt
            (ActionShape.cons C.Y tail) C.Q C.hom C.injective C.transitive rfl
          have hcost := CFSGSolubleOrbitNumerics.block_recurrence
            C.localDegree (Fintype.card C.Y) C.local_ge_two C.top_ge_two
          rw [← C.degree_product] at hcost
          have hstep := C.generators
          change (genRank C.Q : ℝ) ≤
            1280 * (orbitWeight (Fintype.card C.Y) + tail.weight orbitWeight) at hQ
          change (genRank A : ℝ) ≤
            1280 * (orbitWeight (Fintype.card X) + tail.weight orbitWeight)
          have hcost' :
              (traceyInducedGeneratorCeiling 1 (Fintype.card C.Y) : ℝ) *
                  ((Real.logb 2 C.localDegree)^2 + Real.logb 2 C.localDegree) +
                1280 * orbitWeight (Fintype.card C.Y) ≤
                  1280 * orbitWeight (Fintype.card X) := by
            simpa only [orbitWeight, mul_div_assoc] using hcost
          nlinarith

end SymmetricSubgroupAsymptotics.CFSGSolubleOrbitConsequences
