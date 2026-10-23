import SymmetricSubgroupAsymptotics.CFSGOpposedSubgroupKernel
import SymmetricSubgroupAsymptotics.CFSGE6GeckGeneratedParabolics
import SymmetricSubgroupAsymptotics.CFSGE6GeckRelativeSimpleHom
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckRelativeOpposition
import SymmetricSubgroupAsymptotics.CFSGSubgroupConjugateRestriction

/-! On the actual fixed-root-generated E6 group, injectivity on U and
disjoint images of U and V imply a central kernel. Strict upper
overgroups contain an actual simple Weyl word, which moves a nontrivial
parameter-one element from U into V. This recognizes the image upper
normalizer without assuming global representation faithfulness. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGE6GeckOpposedImageKernel
open CFSGOpposedSubgroupKernel CFSGE6GeckGeneratedParabolics
open CFSGE6GeckIntermediateOvergroup CFSGE6GeckRelativeSimpleHom
open CFSGE6GeckSignedSimpleParameters CFSGTwistedE6GeckDiagramCovariance
open CFSGTwistedE6GeckRelativeRootGenerated CFSGTwistedE6GeckRootGeneratedPGroup
open CFSGTwistedE6GeckFixedRangePreimage CFSGTwistedE6GeckRelativeOpposition
open CFSGSubgroupConjugateRestriction CFSGSerreQuadraticWeylWord CFSGTwistedE6RelativeWeylOrbits
variable (K : Type) [Field K] [Finite K] (sigma : K ≃+* K)
local notation "J" => fixedRootGenerated K sigma

omit [Finite K] in
private theorem rawOrbitHom_injective (neg : Bool) (a : Fin 4) :
    Function.Injective (rawOrbitHom K sigma neg a) := by
  fin_cases a
  · exact rawPaired_injective K sigma neg 0
  · exact rawPaired_injective K sigma neg 1
  · exact rawSingleton_injective K neg 1
  · exact rawSingleton_injective K neg 0

include sigma in
omit [Finite K] in
private theorem orbitParameter_one_ne_one (neg : Bool) (a : Fin 4) :
    orbitParameter K neg a 1 ≠ 1 := by
  rw [← rawOrbitHom_one_parameter K sigma neg a]
  intro h
  have hz := rawOrbitHom_injective K sigma neg a (h.trans (map_one _).symm)
  exact one_ne_zero (congrArg Multiplicative.toAdd hz)

include sigma in
omit [Finite K] in
private theorem orbitParameter_reflection (a : Fin 4) :
    canonicalWord rawData K (orbitWord a) * orbitParameter K false a 1 *
      (canonicalWord rawData K (orbitWord a))⁻¹ = orbitParameter K true a (-1) := by
  have h := rawOrbitHom_reflection K sigma a
  rw [rawOrbitHom_one_parameter] at h
  have hi : (rawOrbitHom K sigma true a (Multiplicative.ofAdd 1))⁻¹ =
      rawOrbitHom K sigma true a (Multiplicative.ofAdd (-1)) :=
    (map_inv (rawOrbitHom K sigma true a) (Multiplicative.ofAdd 1)).symm
  rw [hi, rawOrbitHom_neg_one_parameter] at h
  exact h

private def simpleOne (neg : Bool) (a : Fin 4) : J :=
  ⟨orbitParameter K neg a 1, orbitParameter_mem_generated K sigma neg a 1 (map_one sigma)⟩

omit [Finite K] in
private theorem simpleOne_mem_rootPart (neg : Bool) (a : Fin 4) :
    simpleOne K sigma neg a ∈ rootPart K sigma neg :=
  ⟨orbitParameter_mem_upper K neg a 1, orbitParameter_fixed K sigma neg a 1 (map_one sigma)⟩

theorem upper_overgroup_opposed_witness (L : Subgroup J)
    (hBL : upperGenerated K sigma < L) :
    ∃ n ∈ L, ∃ u ∈ rootPart K sigma false,
      n * u * n⁻¹ ∈ rootPart K sigma true ∧ n * u * n⁻¹ ≠ 1 := by
  have hs := (Subgroup.map_lt_map_iff_of_injective (J).subtype_injective).mpr hBL
  rw [upperGenerated_map] at hs
  obtain ⟨a, ha⟩ := exists_simple_weyl_mem_of_upperIn_lt K sigma J (L.map (J).subtype)
    le_rfl (fixedRootGenerated_le_preimage K sigma) hs (Subgroup.map_subtype_le L)
  obtain ⟨n, hn, hnval⟩ := ha
  have hnval' : n.val = canonicalWord rawData K (orbitWord a) := hnval
  refine ⟨n, hn, simpleOne K sigma false a, simpleOne_mem_rootPart K sigma false a, ?_, ?_⟩
  · change n.val * orbitParameter K false a 1 * n.val⁻¹ ∈ signedFixed K sigma true
    rw [hnval', orbitParameter_reflection K sigma a]
    exact ⟨orbitParameter_mem_upper K true a (-1),
      orbitParameter_fixed K sigma true a (-1) (by simp)⟩
  · intro he
    have hconj : (MulAut.conj n) (simpleOne K sigma false a) = (MulAut.conj n) 1 := by
      simpa only [map_one] using he
    have hraw := congrArg Subtype.val ((MulAut.conj n).injective hconj)
    exact orbitParameter_one_ne_one K sigma false a hraw

theorem kernel_le_upper {Q : Type*} [Group Q] (f : J →* Q)
    (hinjU : Set.InjOn f (rootPart K sigma false : Set J))
    (hdisjoint : (rootPart K sigma false).map f ⊓ (rootPart K sigma true).map f = ⊥) :
    f.ker ≤ upperGenerated K sigma := by
  apply CFSGOpposedSubgroupKernel.kernel_le_upper f
    (rootPart K sigma false) (rootPart K sigma true) (upperGenerated K sigma) ?_
    hdisjoint hinjU (upper_overgroup_opposed_witness K sigma)
  intro b hb
  change f b ∈ Subgroup.normalizer ((rootPart K sigma false).map f : Set Q)
  apply (rootPart K sigma false).le_normalizer_map f
  exact ⟨b, (le_of_eq (upperGenerated_eq_normalizer K sigma)) hb, rfl⟩

def oppositionInGenerated : J := ⟨relativeOpposition K, relativeOpposition_mem_generated K sigma⟩

theorem rootPart_opposition :
    (rootPart K sigma false).map (MulAut.conj (oppositionInGenerated K sigma)).toMonoidHom =
      rootPart K sigma true :=
  restrict_conjugate J _ _ (signedFixed_le_generated K sigma false)
    (signedFixed_le_generated K sigma true) (oppositionInGenerated K sigma)
    (fixed_positive_image_eq_fixed_negative K sigma)

theorem kernel_le_center {Q : Type*} [Group Q] (f : J →* Q)
    (hinjU : Set.InjOn f (rootPart K sigma false : Set J))
    (hdisjoint : (rootPart K sigma false).map f ⊓ (rootPart K sigma true).map f = ⊥) :
    f.ker ≤ Subgroup.center J := by
  apply kernel_le_center_of_injective_conjugate_generators f (rootPart K sigma false)
    (oppositionInGenerated K sigma) ?_ hinjU ?_
  · exact (kernel_le_upper K sigma f hinjU hdisjoint).trans
      (le_of_eq (upperGenerated_eq_normalizer K sigma))
  · rw [rootPart_opposition, rootPart_sup]

end SymmetricSubgroupAsymptotics.CFSGE6GeckOpposedImageKernel
