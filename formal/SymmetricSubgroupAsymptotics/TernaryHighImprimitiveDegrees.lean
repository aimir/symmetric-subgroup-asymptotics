import SymmetricSubgroupAsymptotics.C1ImprimitiveNumerics
import SymmetricSubgroupAsymptotics.OriginalMinimalBlock
import SymmetricSubgroupAsymptotics.PermutationChiefWeight
import SymmetricSubgroupAsymptotics.PrimitiveTernaryThreeTenthsWeight
import SymmetricSubgroupAsymptotics.TransitiveTernaryStability

/-!
# High imprimitive ternary pairs have one of five bounded degrees

The actual minimal-block recurrence is combined with the integer ternary
width `B(s)` and the transitive top stability envelope.  The proof keeps the
literal primitive component, literal faithful top image, and original normal
top image.  It reduces every imprimitive pair above `3/20` to total degree
`6`, `9`, `12`, `18`, or `27`.

The only primitive weight premise beyond the uniform `r/3` input is the
three-tenths bound outside degree nine.  It is stated at the exact faithful
primitive-action scope needed by the block recurrence; its finite and
published-tail verification remains a separate named obligation.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- Above the relative `3/20` line, an imprimitive faithful transitive
action has one of the five degrees delegated to the bounded certificates
and the degree-27 structural fork. -/
theorem ternaryHigh_imprimitive_degree_menu
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    {A Ω : Type} [Group A] [Finite A] [Finite Ω] [MulAction A Ω]
    [FaithfulSMul A Ω] [MulAction.IsPretransitive A Ω]
    (N : Subgroup A) [N.Normal]
    (himprimitive : ¬ MulAction.IsPreprimitive A Ω)
    (hhigh : 3 * Nat.card Ω <
      20 * Module.finrank (ZMod 3) (primeRelativeCharacters 3 N)) :
    Nat.card Ω = 6 ∨ Nat.card Ω = 9 ∨ Nat.card Ω = 12 ∨
      Nat.card Ω = 18 ∨ Nat.card Ω = 27 := by
  have hΩtwo : 2 ≤ Nat.card Ω := by
    by_contra h
    have hsmall : Nat.card Ω ≤ 1 := by omega
    letI : Subsingleton Ω := Finite.card_le_one_iff_subsingleton.mp hsmall
    have hz := primeRelativeHead_subsingleton_action (A := A) (Ω := Ω) 3 N
    omega
  letI : Nontrivial Ω := Finite.one_lt_card_iff_nontrivial.mp hΩtwo
  let ω₀ : Ω := Classical.choice inferInstance
  let D : OriginalMinimalBlock (A := A) ω₀ :=
    Classical.choice (originalMinimalBlock_nonempty ω₀ himprimitive)
  let r := Nat.card D.Fibre
  let s := Nat.card D.Points
  have hr : 2 ≤ r := by simpa only [r] using D.degrees_ge_two.1
  have hs : 2 ≤ s := by simpa only [s] using D.degrees_ge_two.2
  have hrs : r * s = Nat.card Ω := by simpa only [r, s] using D.degree_product
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
  have hv3 : 3 * v ≤ r := by
    have h := (Nat.le_div_iff_mul_le (by omega : 0 < 3)).mp hv
    omega
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
  have hhigh' : 3 * (r * s) < 20 * d := by
    simpa only [hrs, d] using hhigh
  by_cases hr2 : r = 2
  · have hv0 : v = 0 := by
      apply permutationChiefWeight_eq_zero_of_card_le_two D.Component c
      simpa only [r] using hr2.le
    by_cases hs3 : s = 3
    · left
      simpa only [r, s, hr2, hs3] using hrs.symm
    · have hsafe := ternaryStability_binary_high_exclusion s hs hs3
      have hdt : d ≤ t := by simpa only [hv0, zero_mul, zero_add] using hd
      simp only [hr2] at hhigh'
      omega
  by_cases hr3 : r = 3
  · by_cases hs2 : s = 2
    · left
      simpa only [r, s, hr3, hs2] using hrs.symm
    by_cases hs3 : s = 3
    · exact Or.inr (Or.inl (by
        simpa only [r, s, hr3, hs3] using hrs.symm))
    by_cases hs4 : s = 4
    · exact Or.inr (Or.inr (Or.inl (by
        simpa only [r, s, hr3, hs4] using hrs.symm)))
    by_cases hs6 : s = 6
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by
        simpa only [r, s, hr3, hs6] using hrs.symm))))
    by_cases hs9 : s = 9
    · exact Or.inr (Or.inr (Or.inr (Or.inr (by
        simpa only [r, s, hr3, hs9] using hrs.symm))))
    have hscalar := ternaryStability_ternary_high_scalar s hs hs2 hs3 hs4 hs6 hs9
    have hv1 : v ≤ 1 := by omega
    have hd' : d ≤ ternaryIndexWidth s + ternaryStabilityBound s := by
      calc
        d ≤ v * ternaryIndexWidth s + t := hd
        _ ≤ 1 * ternaryIndexWidth s + ternaryStabilityBound s :=
          Nat.add_le_add (Nat.mul_le_mul_right _ hv1) ht
        _ = ternaryIndexWidth s + ternaryStabilityBound s := by omega
    have hfloor : 20 * d ≤ 9 * s := by
      have hdiv := hd'.trans hscalar
      have hm := (Nat.le_div_iff_mul_le (by omega : 0 < 20)).mp hdiv
      omega
    simp only [hr3] at hhigh'
    omega
  have hr4 : 4 ≤ r := by omega
  by_cases hs2 : s = 2
  · by_cases hr9 : r = 9
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by
        simpa only [r, s, hr9, hs2] using hrs.symm))))
    have hw := hWeight D.Component D.Fibre hr4 (by simpa only [r] using hr9) c
    have ht0 : t = 0 := by
      have := ht
      simp only [hs2, ternaryStabilityBound_two] at this
      omega
    have hdv : d ≤ v := by
      simpa only [hs2, ternaryIndexWidth_two, mul_one, ht0, add_zero] using hd
    have hw' : 10 * v ≤ 3 * r := by simpa only [v, r] using hw
    simp only [hs2] at hhigh'
    omega
  by_cases hs3 : s = 3
  · by_cases hr4eq : r = 4
    · exact Or.inr (Or.inr (Or.inl (by
        simpa only [r, s, hr4eq, hs3] using hrs.symm)))
    by_cases hr6eq : r = 6
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by
        simpa only [r, s, hr6eq, hs3] using hrs.symm))))
    have ht1 : t ≤ 1 := by simpa only [hs3, ternaryStabilityBound_three] using ht
    have hd' : d ≤ v + 1 := by
      exact hd.trans (by simpa only [hs3, ternaryIndexWidth_three, mul_one] using
        Nat.add_le_add_left ht1 v)
    by_cases hr5eq : r = 5
    · have hv1 : v ≤ 1 := by omega
      simp only [hs3, hr5eq] at hhigh'
      omega
    · have hr7 : 7 ≤ r := by omega
      simp only [hs3] at hhigh'
      omega
  by_cases hs4 : s = 4
  · have ht1 : t ≤ 1 := by simpa only [hs4, ternaryStabilityBound_four] using ht
    have hd' : d ≤ v + 1 := by
      exact hd.trans (by simpa only [hs4, ternaryIndexWidth_four, mul_one] using
        Nat.add_le_add_left ht1 v)
    simp only [hs4] at hhigh'
    omega
  by_cases hs9 : s = 9
  · have ht2 : t ≤ 2 := by simpa only [hs9, ternaryStabilityBound_nine] using ht
    have hd' : d ≤ 3 * v + 2 := by
      have h := hd.trans (Nat.add_le_add_left ht2 (v * ternaryIndexWidth s))
      simpa only [hs9, ternaryIndexWidth_nine, Nat.mul_comm] using h
    by_cases hr5 : r ≤ 5
    · have hv1 : v ≤ 1 := by
        simpa only [v, r] using
          (permutationChiefWeight_le_one_of_card_le_five D.Component c (by
            simpa only [r] using hr5))
      simp only [hs9] at hhigh'
      omega
    · have hr6 : 6 ≤ r := by omega
      simp only [hs9] at hhigh'
      omega
  have hs3le : 3 ≤ s := by omega
  have hB3 : 3 * ternaryIndexWidth s ≤ s := by
    have h := (Nat.le_div_iff_mul_le (by omega : 0 < 3)).mp
      (ternaryIndexWidth_le_third s hs3le)
    omega
  have htOrd : t ≤ 5 * s / 27 := by
    simpa only [t, s, T] using
      (transitiveTernaryHead_stability_ordinary hChief hPrimitive h18 T
        hs3 hs4 hs9)
  have ht27 : 27 * t ≤ 5 * s := by
    have h := (Nat.le_div_iff_mul_le (by omega : 0 < 27)).mp htOrd
    omega
  by_cases hr4eq : r = 4
  · have hv1 : v ≤ 1 := by omega
    have hsafe := c1_imprimitive_ordinary_four s v (ternaryIndexWidth s) t d
      (by omega) hv1 hB3 ht27 hd
    simp only [hr4eq] at hhigh'
    omega
  · have hr5 : 5 ≤ r := by omega
    have hsafe := c1_imprimitive_ordinary_large r s v (ternaryIndexWidth s) t d
      hr5 (by omega) hv3 hB3 ht27 hd
    omega

end SymmetricSubgroupAsymptotics

end
