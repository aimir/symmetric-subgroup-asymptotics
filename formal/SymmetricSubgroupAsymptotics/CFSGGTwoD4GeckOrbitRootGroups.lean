import SymmetricSubgroupAsymptotics.CFSGTrialityGeckNegativeOrbitRootGroups

/-! The two identity-twist simple orbit groups have literal K-parameter
charts. A fixed simple Weyl word carries each whole positive chart to
its negative chart. No cubic-norm or fixed-quotient surjectivity is used. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOrbitRootGroups
open CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance
open CFSGTrialityGeckOrbitZeroFunctionalGroup CFSGTrialityGeckFixedOrbitRootGroups
open CFSGTrialityGeckNegativeOrbitRootGroups CFSGTrialityGeckShortComplementFactor
open CFSGTrialityGeckFixedShortComplementFactor CFSGTrialityGeckShortCentralizerCardinality
open CFSGTrialityGeckFixedRootWords CFSGTrialityFixedWeylWords CFSGTrialityGeckSimpleOrbitFlags
open CFSGTrialityGeckRootSubgroupTwist CFSGTrialityGeckMatrixTwist
open CFSGCentralTwistedCommutatorLift CFSGFixedSubgroupConjugation
open CFSGSerreQuadraticMatrix CFSGSerreQuadraticWeylWord
variable (K : Type) [Field K] [Finite K]

def fixedOrbitPositive (a : Bool) : Subgroup (Matrix GeckIndex GeckIndex K)ˣ :=
  orbitRootGroup K a ⊓ fixedSubgroup (unitTwist K (RingEquiv.refl K))

def fixedOrbitNegative (a : Bool) : Subgroup (Matrix GeckIndex GeckIndex K)ˣ :=
  orbitNegativeGroup K a ⊓ fixedSubgroup (unitTwist K (RingEquiv.refl K))

def positiveParameter (a : Bool) (t : K) : fixedOrbitPositive K a := by
  cases a
  · exact ⟨shortOrbit K (RingEquiv.refl K) false t,
      shortOrbit_mem_outer K (RingEquiv.refl K) t,
      shortOrbit_fixed K (RingEquiv.refl K) false t rfl⟩
  · refine ⟨canonicalRoot rawData K false 1 t, ⟨t, rfl⟩, ?_⟩
    change unitTwist K (RingEquiv.refl K) (canonicalRoot rawData K false 1 t) =
      canonicalRoot rawData K false 1 t
    rw [unitTwist_raw_root]
    rfl

theorem positiveParameter_bijective (a : Bool) : Function.Bijective (positiveParameter K a) := by
  cases a
  · constructor
    · intro t u he
      exact shortOrbit_injective K (RingEquiv.refl K) (congrArg Subtype.val he)
    · intro u
      obtain ⟨t, _, he⟩ := exists_short_orbit_of_outer_fixed K (RingEquiv.refl K)
        u.val u.property.1 u.property.2
      exact ⟨t, Subtype.ext he.symm⟩
  · constructor
    · intro t u he
      exact canonical_middle_injective K (congrArg Subtype.val he)
    · intro u
      obtain ⟨t, ht⟩ := u.property.1
      exact ⟨t, Subtype.ext ht⟩

theorem fixedOrbitPositive_map (a : Bool) :
    (fixedOrbitPositive K a).map
      (MulAut.conj (canonicalWord rawData K (orbitWord a))).toMonoidHom =
        fixedOrbitNegative K a := by
  have hW : unitTwist K (RingEquiv.refl K) (canonicalWord rawData K (orbitWord a)) =
      canonicalWord rawData K (orbitWord a) := by
    cases a
    · exact shortWeyl_fixed K (RingEquiv.refl K)
    · exact longWeyl_fixed K (RingEquiv.refl K)
  rw [fixedOrbitPositive, map_inf_fixed _ _ _ hW, orbit_word_map_positive]
  rfl

theorem fixedOrbitPositive_card (a : Bool) : Nat.card (fixedOrbitPositive K a) = Nat.card K :=
  (Nat.card_congr (Equiv.ofBijective (positiveParameter K a)
    (positiveParameter_bijective K a))).symm

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOrbitRootGroups
