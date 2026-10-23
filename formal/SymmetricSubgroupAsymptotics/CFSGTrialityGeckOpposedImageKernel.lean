import SymmetricSubgroupAsymptotics.CFSGOpposedSubgroupKernel
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckGeneratedParabolics
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedOrbitRootGroups
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckSimpleChartWeyl
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckShortCentralizerCardinality
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckRelativeOpposition
import SymmetricSubgroupAsymptotics.CFSGSubgroupConjugateRestriction

/-! On the actual D4 fixed-root-generated group, injectivity on its
positive part and disjoint opposite images force a central kernel.
The strict upper-overgroup test and the parameter-one reflection are
literal checked matrix words. No full-source faithfulness, diagonal
recognition, or original automorphism lifting is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckOpposedImageKernel
open CFSGOpposedSubgroupKernel CFSGTrialityGeckGeneratedParabolics
open CFSGTrialityGeckIntermediateOvergroup CFSGTrialityGeckOvergroupWeylExtraction
open CFSGTrialityGeckFixedOrbitRootGroups CFSGTrialityGeckSimpleChartWeyl
open CFSGTrialityGeckShortCentralizerCardinality CFSGTrialityGeckShortOrbitCommutator
open CFSGTrialityGeckFixedRootWords CFSGTrialityGeckDiagramCovariance
open CFSGTrialityGeckRelativeRootGenerated CFSGTrialityGeckRootGeneratedPGroup
open CFSGTrialityGeckFixedUpperNormalizer CFSGTrialityGeckRelativeOpposition
open CFSGSubgroupConjugateRestriction CFSGSerreQuadraticMatrix CFSGSerreQuadraticWeylWord
open CFSGTrialityGeckSimpleOrbitFlags
variable (K : Type) [Field K] [Finite K] (sigma : K≃+*K)
local notation "J" => fixedRootGenerated K sigma

private theorem orbitParameter_one_ne_one (a : Bool) :
    orbitParameter K sigma false a 1≠1 := by
  cases a
  · change shortOrbit K sigma false 1≠1
    intro he
    exact one_ne_zero (shortOrbit_injective K sigma
      (he.trans (shortOrbit_zero K sigma false).symm))
  · change canonicalRoot rawData K false 1 1≠1
    intro he
    exact one_ne_zero (canonical_middle_injective K
      (he.trans (canonicalRoot_zero rawData K false 1).symm))

private theorem orbitParameter_reflection (a : Bool) :
    canonicalWord rawData K (orbitWord a)*orbitParameter K sigma false a 1*
      (canonicalWord rawData K (orbitWord a))⁻¹=orbitParameter K sigma true a (-1) := by
  cases a
  · exact short_word_conjugates K sigma 1
  · exact middle_word_conjugates K 1

private def simpleOne (neg : Bool) (a : Bool) : J :=
  ⟨orbitParameter K sigma neg a 1,
    signedFixed_le_generated K sigma neg (orbitParameter_one_mem_signedFixed K sigma neg a)⟩

private theorem simpleOne_mem_rootPart (neg : Bool) (a : Bool) :
    simpleOne K sigma neg a∈rootPart K sigma neg :=
  orbitParameter_one_mem_signedFixed K sigma neg a

theorem upper_overgroup_opposed_witness (L : Subgroup J)
    (hBL : upperGenerated K sigma<L) :
    ∃n∈L,∃u∈rootPart K sigma false,
      n*u*n⁻¹∈rootPart K sigma true ∧ n*u*n⁻¹≠1 := by
  have hs := (Subgroup.map_lt_map_iff_of_injective (J).subtype_injective).mpr hBL
  rw [upperGenerated_map] at hs
  obtain ⟨a,ha⟩ := exists_simple_weyl_mem_of_upperIn_lt K sigma J (L.map (J).subtype)
    le_rfl (fixedRootGenerated_le_fixedRaw K sigma) hs (Subgroup.map_subtype_le L)
  obtain ⟨n,hn,hnval⟩ := ha
  have hnval' : n.val=canonicalWord rawData K (orbitWord a) := hnval
  refine ⟨n,hn,simpleOne K sigma false a,simpleOne_mem_rootPart K sigma false a,?_,?_⟩
  · change n.val*orbitParameter K sigma false a 1*n.val⁻¹∈signedFixed K sigma true
    rw [hnval',orbitParameter_reflection]
    rw [orbitParameter_neg]
    exact (signedFixed K sigma true).inv_mem (orbitParameter_one_mem_signedFixed K sigma true a)
  · intro he
    have hconj : (MulAut.conj n) (simpleOne K sigma false a)=(MulAut.conj n) 1 := by
      simpa only [map_one] using he
    have hraw := congrArg (fun z : J=>z.val) ((MulAut.conj n).injective hconj)
    exact orbitParameter_one_ne_one K sigma a hraw

theorem kernel_le_upper {Q : Type*} [Group Q] (f : J→*Q)
    (hinjU : Set.InjOn f (rootPart K sigma false : Set J))
    (hdisjoint : (rootPart K sigma false).map f ⊓ (rootPart K sigma true).map f=⊥) :
    f.ker≤upperGenerated K sigma := by
  apply CFSGOpposedSubgroupKernel.kernel_le_upper f
    (rootPart K sigma false) (rootPart K sigma true) (upperGenerated K sigma) ?_
    hdisjoint hinjU (upper_overgroup_opposed_witness K sigma)
  intro b hb
  change f b∈Subgroup.normalizer ((rootPart K sigma false).map f : Set Q)
  apply (rootPart K sigma false).le_normalizer_map f
  exact ⟨b,(le_of_eq (upperGenerated_eq_normalizer K sigma)) hb,rfl⟩

def oppositionInGenerated : J :=
  ⟨relativeOpposition K,relativeOpposition_mem_generated K sigma⟩

theorem rootPart_opposition :
    (rootPart K sigma false).map (MulAut.conj (oppositionInGenerated K sigma)).toMonoidHom=
      rootPart K sigma true :=
  restrict_conjugate J _ _ (signedFixed_le_generated K sigma false)
    (signedFixed_le_generated K sigma true) (oppositionInGenerated K sigma)
    (fixed_positive_image_eq_fixed_negative K sigma)

theorem kernel_le_center {Q : Type*} [Group Q] (f : J→*Q)
    (hinjU : Set.InjOn f (rootPart K sigma false : Set J))
    (hdisjoint : (rootPart K sigma false).map f ⊓ (rootPart K sigma true).map f=⊥) :
    f.ker≤Subgroup.center J := by
  apply kernel_le_center_of_injective_conjugate_generators f (rootPart K sigma false)
    (oppositionInGenerated K sigma) ?_ hinjU ?_
  · exact (kernel_le_upper K sigma f hinjU hdisjoint).trans
      (le_of_eq (upperGenerated_eq_normalizer K sigma))
  · rw [rootPart_opposition,rootPart_sup]

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckOpposedImageKernel
