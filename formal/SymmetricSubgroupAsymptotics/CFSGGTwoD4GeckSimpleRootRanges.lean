import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckNegativeParabolicIntersection
import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckSimpleParameters

/-! The actual signed orbit-zero subgroups of J(K,id) are precisely
the ranges of their literal additive parameter homomorphisms. The
negative range is transported by an actual fixed Weyl word. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckSimpleRootRanges
open CFSGGTwoD4GeckOrbitRootGroups CFSGGTwoD4GeckSimpleParameters
open CFSGGTwoD4GeckNegativeParabolicIntersection
open CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance CFSGTrialityGeckSimpleOrbitFlags
open CFSGTrialityGeckSimpleChartWeyl CFSGSerreQuadraticWeylWord
variable (K : Type) [Field K] [Finite K]

theorem positiveParameter_val_eq (a : Bool) (t : K) :
    (positiveParameter K a t).val =
      (simpleGeneratedHom K false a (Multiplicative.ofAdd t)).val := by
  cases a <;> rfl

theorem simple_word_conjugates (a : Bool) (t : K) :
    canonicalWord rawData K (orbitWord a) *
      (simpleGeneratedHom K false a (Multiplicative.ofAdd t)).val *
        (canonicalWord rawData K (orbitWord a))⁻¹ =
      (simpleGeneratedHom K true a (Multiplicative.ofAdd (-t))).val := by
  cases a
  · exact short_word_conjugates K (RingEquiv.refl K) t
  · exact middle_word_conjugates K t

theorem positive_generated_eq_range (a : Bool) :
    positiveOrbitRootGenerated K a = (simpleGeneratedHom K false a).range := by
  ext g
  constructor
  · intro hg
    have hm : g.val ∈ fixedOrbitPositive K a := hg
    obtain ⟨t, ht⟩ := (positiveParameter_bijective K a).2 ⟨g.val, hm⟩
    refine ⟨Multiplicative.ofAdd t, Subtype.ext ?_⟩
    exact (positiveParameter_val_eq K a t).symm.trans
      (congrArg (fun x : fixedOrbitPositive K a => x.val) ht)
  · rintro ⟨t, rfl⟩
    change (simpleGeneratedHom K false a (Multiplicative.ofAdd t.toAdd)).val ∈
      fixedOrbitPositive K a
    rw [←positiveParameter_val_eq K a t.toAdd]
    exact (positiveParameter K a t.toAdd).property

theorem negative_generated_eq_range (a : Bool) :
    negativeOrbitRootGenerated K a = (simpleGeneratedHom K true a).range := by
  ext g
  constructor
  · intro hg
    have hm : g.val ∈ fixedOrbitNegative K a := hg
    rw [←fixedOrbitPositive_map K a] at hm
    obtain ⟨x, hx, hxg⟩ := hm
    obtain ⟨t, ht⟩ := (positiveParameter_bijective K a).2 ⟨x, hx⟩
    have hxt : (simpleGeneratedHom K false a (Multiplicative.ofAdd t)).val = x :=
      (positiveParameter_val_eq K a t).symm.trans
        (congrArg (fun z : fixedOrbitPositive K a => z.val) ht)
    refine ⟨Multiplicative.ofAdd (-t), Subtype.ext ?_⟩
    calc
      _ = canonicalWord rawData K (orbitWord a) * x *
          (canonicalWord rawData K (orbitWord a))⁻¹ := by
        rw [←hxt]
        exact (simple_word_conjugates K a t).symm
      _ = g.val := hxg
  · rintro ⟨t, rfl⟩
    change (simpleGeneratedHom K true a t).val ∈ fixedOrbitNegative K a
    rw [←fixedOrbitPositive_map K a]
    have hx : (simpleGeneratedHom K false a (Multiplicative.ofAdd (-t.toAdd))).val ∈
        fixedOrbitPositive K a := by
      have hh : simpleGeneratedHom K false a (Multiplicative.ofAdd (-t.toAdd)) ∈
          positiveOrbitRootGenerated K a := by
        rw [positive_generated_eq_range]
        exact ⟨Multiplicative.ofAdd (-t.toAdd), rfl⟩
      exact hh
    refine ⟨(simpleGeneratedHom K false a (Multiplicative.ofAdd (-t.toAdd))).val, hx, ?_⟩
    simpa only [neg_neg] using simple_word_conjugates K a (-t.toAdd)

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckSimpleRootRanges
