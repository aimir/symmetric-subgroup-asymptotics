import SymmetricSubgroupAsymptotics.CFSGSufficientTernaryStability
import SymmetricSubgroupAsymptotics.CFSGSufficientSmallPrimitiveHeadsDirect
import SymmetricSubgroupAsymptotics.CFSGSufficientTenTwelveHeads
import SymmetricSubgroupAsymptotics.TransitiveTernaryRelaxedStabilityWithoutCatalogue
import SymmetricSubgroupAsymptotics.TransitiveTernaryStabilityAwayFromTen
import SymmetricSubgroupAsymptotics.TernaryRelaxedHighImprimitiveDegrees
import SymmetricSubgroupAsymptotics.TernaryRelaxedHighActionDegrees

/-! Direct actual-head forwarding; the ordinary primitive normal-generator input is absent.

 The actual minimal-block stability induction from sufficient primitive
bounds. The original finite exceptions, normal image, block fibre and
relative-character heads are unchanged; no global strict-head input appears.
This also retains the exact high-degree menu used by physical continuation. -/

/-! A complete actual-action stability theorem sufficient for the enlarged
high-orbit frontier. It relaxes degree10 to2 and retains every original
normal subgroup in the minimal-block induction. No strict-head premise or
primitive composition correspondence is introduced. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
open PrimitiveSocleRawStructure
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

theorem primitiveTernary_relaxed_stability_input_of_sufficientHead
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r/3))
     (hindex : SufficientSimpleIndexBounds)
    (published8 : DegreeEightCanonicalCatalogue.PublishedClassification) :
    PrimitiveTernaryHeadBoundOutside ternaryRelaxedStabilityBound ({18} : Finset ℕ) := by
  intro G X _ _ _ _ _ _ _ hF N _
  have h18 : Nat.card X≠18 := by simpa only [Finset.mem_singleton] using hF
  by_cases hsmall : Nat.card X=3 ∨ Nat.card X=4
  · obtain ⟨c,hc⟩ := hChief G X
    have hh := (primeRelativeHead_le_actualChiefWeight N c).trans hc
    rcases hsmall with h|h <;>
      simpa only [h,ternaryRelaxedStabilityBound,ternaryStabilityBound] using hh
  by_cases hex : Nat.card X=10 ∨ Nat.card X=12
  · cases Classical.choice (publishedONanScottStructure G X) with
    | inl D =>
        have hh := D.ten_twelve_relativeHead_le_two_of_sufficient hindex hex N
        rcases hex with h|h <;>
          simpa only [h,ternaryRelaxedStabilityBound,ternaryStabilityBound] using hh
    | inr P =>
        have hs := P.small_ternaryRelativeHead_strict inferInstance (by omega)
          (by omega) (by omega) N
        have hh := ternaryStrictHead_le_stability_base _ _ hs
        exact hh.trans ((ternaryStability_base_le _ h18).trans
          (ternaryStability_le_relaxed _))
  have hs := primitiveTernaryStrictHead_awayFromTenTwelve_of_sufficientHead
     hindex published8 G X (by omega) (by omega) (by omega) (by omega) N
  exact (ternaryStrictHead_le_stability_base _ _ hs).trans
    ((ternaryStability_base_le _ h18).trans (ternaryStability_le_relaxed _))

/-- Degree10 is the only changed value; degree12 already had head bound2. -/
theorem transitiveTernaryHead_relaxed_stability_of_sufficientHead
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r/3))
     (hindex : SufficientSimpleIndexBounds)
    (published8 : DegreeEightCanonicalCatalogue.PublishedClassification)
    (h18 : DegreeEighteenTernaryHeadBound)
    {A X : Type} [Group A] [Finite A] [Finite X] [MulAction A X]
    [FaithfulSMul A X] [MulAction.IsPretransitive A X] [Nonempty X]
    (N : Subgroup A) [N.Normal] :
    Module.finrank (ZMod 3) (primeRelativeCharacters 3 N)≤
      ternaryRelaxedStabilityBound (Nat.card X) := by
  apply transitiveTernaryHead_bound_with_finite_bypass
    ternaryRelaxedStabilityBound (fun r => r/3) ({18} : Finset ℕ) ?_
    (primitiveTernary_relaxed_stability_input_of_sufficientHead hChief  hindex published8)
    hChief ?_ N
  · intro G Y _ _ _ _ _ _ _ hY M _
    have hy : Nat.card Y=18 := by simpa only [Finset.mem_singleton] using hY
    simpa only [hy,ternaryRelaxedStabilityBound,ternaryStabilityBound] using h18 G Y hy M
  · intro r s hr hs hf
    exact ternaryRelaxedStability_scalar r s hr hs
      (by simpa only [Finset.mem_singleton] using hf)

end SymmetricSubgroupAsymptotics


/-! Away from degree10 the proved relaxed bound is the original stability
envelope. This adapter is used only with actual displayed degree data. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

theorem transitiveTernaryHead_stability_of_sufficientHead_of_ne_ten
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r/3))
    
    (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    (h18 : DegreeEighteenTernaryHeadBound)
    {A X : Type} [Group A] [Finite A] [Finite X] [MulAction A X]
    [FaithfulSMul A X] [MulAction.IsPretransitive A X] [Nonempty X]
    (h10 : Nat.card X≠10) (N : Subgroup A) [N.Normal] :
    Module.finrank (ZMod 3) (primeRelativeCharacters 3 N)≤
      ternaryStabilityBound (Nat.card X) := by
  simpa only [ternaryRelaxedStabilityBound,if_neg h10] using
    transitiveTernaryHead_relaxed_stability_of_sufficientHead
      hChief  hindex published8 h18 (X := X) N

end SymmetricSubgroupAsymptotics


/-! The original five imprimitive high degrees survive the relaxed actual
stability bound. The sole new top value is at10; its actual induced width2
and head2 make every imprimitive parent safe, so no new total degree enters.
The original minimal blocks, chief series and normal top images are kept. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- Above the relative `3/20` line, an imprimitive faithful transitive
action has one of the five degrees delegated to the bounded certificates
and the degree-27 structural fork. -/
theorem ternaryHigh_imprimitive_degree_menu_of_sufficientHead
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    
    (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
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
  have htRelaxed : t ≤ ternaryRelaxedStabilityBound s := by
    simpa only [t, s, T] using
      (transitiveTernaryHead_relaxed_stability_of_sufficientHead
        hChief  hindex published8 h18 T)
  have hhigh' : 3 * (r * s) < 20 * d := by
    simpa only [hrs, d] using hhigh
  by_cases hs10 : s=10
  · have ht2 : t≤2 := by
      simpa only [hs10,ternaryRelaxedStabilityBound] using htRelaxed
    have hd2 : d≤2*v+2 := by
      have hh := hd.trans (Nat.add_le_add_left ht2 (v*ternaryIndexWidth s))
      simpa only [hs10,ternaryIndexWidth_ten,Nat.mul_comm] using hh
    simp only [hs10] at hhigh'
    by_cases hr2 : r=2
    · subst r
      omega
    · have hr3 : 3≤r := by omega
      nlinarith
  have ht : t≤ternaryStabilityBound s := by
    simpa only [ternaryRelaxedStabilityBound,if_neg hs10] using htRelaxed
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
    exact ht.trans (ternaryStability_le_base s hs3 hs4 hs9)
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


/-! The actual high-orbit finite menu without the composition catalogue:
only primitive degree10 is added, and primitive degree12 is retained
separately for its semisimple source. All original normal pairs remain. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

theorem ternaryHigh_action_degree_menu_of_sufficientHead
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r/3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    
    (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    (h18 : DegreeEighteenTernaryHeadBound)
    {A X : Type} [Group A] [Finite A] [Finite X] [MulAction A X]
    [FaithfulSMul A X] [MulAction.IsPretransitive A X]
    (N : Subgroup A) [N.Normal]
    (hhigh : 3*Nat.card X<20*Module.finrank (ZMod 3) (primeRelativeCharacters 3 N)) :
    Nat.card X=3 ∨ Nat.card X=4 ∨ Nat.card X=6 ∨ Nat.card X=9 ∨
      Nat.card X=10 ∨ Nat.card X=12 ∨ Nat.card X=27 := by
  have htwo : 2≤Nat.card X := by
    by_contra h
    letI : Subsingleton X := Finite.card_le_one_iff_subsingleton.mp (by omega)
    have hh := primeRelativeHead_subsingleton_action (A := A) (Ω := X) 3 N
    omega
  letI : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp htwo
  by_cases hp : MulAction.IsPreprimitive A X
  · letI : MulAction.IsPreprimitive A X := hp
    by_cases h3 : Nat.card X=3
    · exact Or.inl h3
    by_cases h4 : Nat.card X=4
    · exact Or.inr (Or.inl h4)
    by_cases h10 : Nat.card X=10
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h10))))
    by_cases h12 : Nat.card X=12
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h12)))))
    have hs := primitiveTernaryStrictHead_awayFromTenTwelve_of_sufficientHead
       hindex published8 A X h3 h4 h10 h12 N
    omega
  · have hm := ternaryHigh_imprimitive_degree_menu_of_sufficientHead
      hChief hWeight  hindex published8 h18 N hp hhigh
    rcases hm with h6|h9|h12|h18x|h27
    · exact Or.inr (Or.inr (Or.inl h6))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h9)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h12)))))
    · have hr := h18 A X h18x N
      omega
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h27)))))

end SymmetricSubgroupAsymptotics
