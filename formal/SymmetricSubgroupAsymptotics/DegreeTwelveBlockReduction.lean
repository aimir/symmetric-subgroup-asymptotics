import SymmetricSubgroupAsymptotics.TernaryHighImprimitiveDegrees

/-!
# Structural reduction of the high degree-twelve branch

An actual minimal block system in degree twelve has factorization
`2 × 6`, `3 × 4`, `4 × 3`, or `6 × 2`.  For a normal pair above the
relative `3/20` line the first and last orientations are impossible.
Moreover, in either surviving orientation the minimal-block head recurrence
is sharp: the chosen primitive fibre chief series has ternary weight one,
the original normal top image has relative ternary rank one, and the original
normal subgroup has relative ternary rank two.

Thus the remaining degree-twelve ownership question is a structural problem
for the two natural geometries `3 × 4` and `4 × 3`; it no longer requires a
blind scan through all 301 transitive actions.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- Every high degree-twelve normal pair has a minimal block system of type
`3 × 4` or `4 × 3`, and all three terms in the resulting head comparison
attain their forced values. -/
theorem degreeTwelve_high_minimalBlock_data
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    {A Ω : Type} [Group A] [Finite A] [Finite Ω] [MulAction A Ω]
    [FaithfulSMul A Ω] [MulAction.IsPretransitive A Ω]
    (N : Subgroup A) [N.Normal]
    (hDegree : Nat.card Ω = 12)
    (hHigh : 3 * Nat.card Ω <
      20 * Module.finrank (ZMod 3) (primeRelativeCharacters 3 N)) :
    ∃ (ω₀ : Ω) (D : OriginalMinimalBlock (A := A) ω₀)
        (c : ActualChiefSeries D.Component),
      ((Nat.card D.Fibre = 3 ∧ Nat.card D.Points = 4) ∨
        (Nat.card D.Fibre = 4 ∧ Nat.card D.Points = 3)) ∧
      actualChiefSeriesTernaryWeight c = 1 ∧
      Module.finrank (ZMod 3)
        (primeRelativeCharacters 3 (originalNormalRange D.topMap N)) = 1 ∧
      Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) = 2 := by
  have hΩtwo : 2 ≤ Nat.card Ω := by omega
  letI : Nontrivial Ω := Finite.one_lt_card_iff_nontrivial.mp hΩtwo
  have himprimitive : ¬ MulAction.IsPreprimitive A Ω := by
    intro hp
    letI : MulAction.IsPreprimitive A Ω := hp
    have hSafe := hPrimitive A Ω (by omega) (by omega) (by omega) N
    omega
  let ω₀ : Ω := Classical.choice inferInstance
  let D : OriginalMinimalBlock (A := A) ω₀ :=
    Classical.choice (originalMinimalBlock_nonempty ω₀ himprimitive)
  let r := Nat.card D.Fibre
  let s := Nat.card D.Points
  have hr : 2 ≤ r := by simpa only [r] using D.degrees_ge_two.1
  have hs : 2 ≤ s := by simpa only [s] using D.degrees_ge_two.2
  have hrs : r * s = 12 := by
    rw [D.degree_product, hDegree]
  letI : Nontrivial D.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp (by simpa only [r] using hr)
  letI : Finite D.Component :=
    Finite.of_surjective
      (originalBlockFibreAction D.map D.map_equivariant D.base).rangeRestrict
      (originalBlockFibreAction D.map D.map_equivariant D.base).rangeRestrict_surjective
  letI : MulAction.IsPreprimitive D.Component D.Fibre := D.component_preprimitive
  obtain ⟨c, hc⟩ := hChief D.Component D.Fibre
  let v := actualChiefSeriesTernaryWeight c
  have hv : v ≤ r / 3 := by simpa only [v, r] using hc
  letI : MulAction.IsPretransitive D.Top D.Points := D.top_pretransitive
  letI : FaithfulSMul D.Top D.Points := D.top_faithful
  letI : Finite D.Top := D.top_finite
  letI : Nonempty D.Points := ⟨D.base⟩
  let T := originalNormalRange D.topMap N
  let t := Module.finrank (ZMod 3) (primeRelativeCharacters 3 T)
  let d := Module.finrank (ZMod 3) (primeRelativeCharacters 3 N)
  have hd : d ≤ v * ternaryIndexWidth s + t := by
    simpa only [d, v, s, t, T] using D.head_bound_nat N c
  have ht : t ≤ ternaryStabilityBound s := by
    simpa only [t, s, T] using
      (transitiveTernaryHead_stability hChief hPrimitive h18 T)
  have hdTwo : 2 ≤ d := by
    change 3 * Nat.card Ω < 20 * d at hHigh
    rw [hDegree] at hHigh
    omega
  have horient : (r = 3 ∧ s = 4) ∨ (r = 4 ∧ s = 3) := by
    have hfactors :
        (r = 2 ∧ s = 6) ∨ (r = 3 ∧ s = 4) ∨
          (r = 4 ∧ s = 3) ∨ (r = 6 ∧ s = 2) := by
      have hrle : r ≤ 6 := by nlinarith
      by_cases hr2 : r = 2
      · exact Or.inl ⟨hr2, by nlinarith⟩
      by_cases hr3 : r = 3
      · exact Or.inr (Or.inl ⟨hr3, by nlinarith⟩)
      by_cases hr4 : r = 4
      · exact Or.inr (Or.inr (Or.inl ⟨hr4, by nlinarith⟩))
      have hr5 : 5 ≤ r := by omega
      have hr6 : r = 6 := by
        by_cases h : r = 5
        · rw [h] at hrs
          omega
        · omega
      exact Or.inr (Or.inr (Or.inr ⟨hr6, by nlinarith⟩))
    rcases hfactors with h26 | h34 | h43 | h62
    · have hv0 : v = 0 := by
        apply permutationChiefWeight_eq_zero_of_card_le_two D.Component c
        change r ≤ 2
        omega
      have ht1 : t ≤ 1 := by
        have := ht
        norm_num [h26.2, ternaryStabilityBound] at this ⊢
        exact this
      have hd1 : d ≤ 1 := by
        rw [h26.2, hv0, zero_mul, zero_add] at hd
        exact hd.trans ht1
      omega
    · exact Or.inl h34
    · exact Or.inr h43
    · have hw := hWeight D.Component D.Fibre (by
            change 4 ≤ r
            omega)
          (by
            change r ≠ 9
            omega) c
      have hv1 : v ≤ 1 := by
        change 10 * v ≤ 3 * r at hw
        omega
      have ht0 : t = 0 := by
        have := ht
        simp only [h62.2, ternaryStabilityBound_two] at this
        omega
      have hd1 : d ≤ 1 := by
        have := hd.trans (Nat.add_le_add_right
          (Nat.mul_le_mul_right (ternaryIndexWidth s) hv1) t)
        simpa only [h62.2, ternaryIndexWidth_two, mul_one, ht0, add_zero] using this
      omega
  have hv1 : v ≤ 1 := by
    rcases horient with h34 | h43
    · simpa only [h34.1] using hv
    · simpa only [h43.1] using hv
  have ht1 : t ≤ 1 := by
    rcases horient with h34 | h43
    · simpa only [h34.2, ternaryStabilityBound_four] using ht
    · simpa only [h43.2, ternaryStabilityBound_three] using ht
  have hwidth : ternaryIndexWidth s = 1 := by
    rcases horient with h34 | h43
    · simp only [h34.2, ternaryIndexWidth_four]
    · simp only [h43.2, ternaryIndexWidth_three]
  have hdUpper : d ≤ 2 := by
    calc
      d ≤ v * ternaryIndexWidth s + t := hd
      _ ≤ 1 * 1 + 1 := Nat.add_le_add
        (Nat.mul_le_mul hv1 (le_of_eq hwidth)) ht1
      _ = 2 := by omega
  have hdEq : d = 2 := by omega
  have hvEq : v = 1 := by
    by_contra hvne
    have hv0 : v = 0 := by omega
    rw [hv0, zero_mul, zero_add] at hd
    omega
  have htEq : t = 1 := by
    by_contra htne
    have ht0 : t = 0 := by omega
    rw [hwidth, mul_one, ht0, add_zero, hdEq] at hd
    omega
  refine ⟨ω₀, D, c, ?_, ?_, ?_, ?_⟩
  · simpa only [r, s] using horient
  · simpa only [v] using hvEq
  · simpa only [t, T] using htEq
  · simpa only [d] using hdEq

end SymmetricSubgroupAsymptotics

end
