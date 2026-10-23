import SymmetricSubgroupAsymptotics.CFSGFFourE6FixedPositiveProjection
import SymmetricSubgroupAsymptotics.CFSGFFourE6RelativeWords
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckRelativeOpposition

/-! Both literal identity-coefficient E6 diagram-fixed upper groups
belong to the SAME folded F4 matrix group. The negative inclusion is
transported by the actual relative opposition word in that group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6SignedFixedInclusion
open CFSGFFourSerreMatrices CFSGFFourE6FixedPositiveProjection CFSGFFourE6RelativeWords
open CFSGTwistedE6GeckRelativeOpposition CFSGTwistedE6RelativeOppositionLattice
open CFSGTwistedE6GeckRelativeRootGenerated CFSGTwistedE6GeckDiagramCovariance
open CFSGNormTwoGeckIntegralWord CFSGSerreQuadraticMatrix

theorem relativeOpposition_mem_folded (K : Type) [Field K] :
    relativeOpposition K∈canonicalElementaryGroup realizationData K := by
  simpa only [relativeOpposition,word_eq_canonicalWord,oppositionWord] using
    relativeWord_mem_folded K oppositionRelativeWord

theorem fixedNegative_mem_folded (K : Type) [Field K] [Finite K]
    (u : signedFixed K (RingEquiv.refl K) true) :
    u.val∈canonicalElementaryGroup realizationData K := by
  have hm := (le_of_eq
    (fixed_positive_image_eq_fixed_negative K (RingEquiv.refl K)).symm) u.property
  obtain ⟨v,hv,he⟩ := hm
  rw [←he]
  have hW := relativeOpposition_mem_folded K
  exact (canonicalElementaryGroup realizationData K).mul_mem
    ((canonicalElementaryGroup realizationData K).mul_mem hW
      (fixedPositive_mem_folded K ⟨v,hv⟩))
    ((canonicalElementaryGroup realizationData K).inv_mem hW)

theorem signedFixed_mem_folded (K : Type) [Field K] [Finite K] (neg : Bool)
    (u : signedFixed K (RingEquiv.refl K) neg) :
    u.val∈canonicalElementaryGroup realizationData K := by
  cases neg
  · exact fixedPositive_mem_folded K u
  · exact fixedNegative_mem_folded K u

def signedFixedToFolded (K : Type) [Field K] [Finite K] (neg : Bool) :
    signedFixed K (RingEquiv.refl K) neg→*canonicalElementaryGroup realizationData K where
  toFun u := ⟨u.val,signedFixed_mem_folded K neg u⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem signedFixedToFolded_injective (K : Type) [Field K] [Finite K] (neg : Bool) :
    Function.Injective (signedFixedToFolded K neg) := by
  intro u v he
  exact Subtype.ext (congrArg (fun z : canonicalElementaryGroup realizationData K=>z.val) he)

end SymmetricSubgroupAsymptotics.CFSGFFourE6SignedFixedInclusion
