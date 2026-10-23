import SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalOppositeAlignment
import SymmetricSubgroupAsymptotics.CFSGConjugateSubgroupHomInjective
import SymmetricSubgroupAsymptotics.CFSGSubgroupConjugateRestriction

/-! Both literal diagram-fixed signed E6 upper groups inject into the
ORIGINAL F4 model. Negative injectivity follows from the actual folded
relative opposition conjugacy and positive projective injectivity. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6SignedOriginalProjection
open CFSGFFourSerreMatrices CFSGFFourE6OriginalProjection CFSGFFourE6FixedPositiveProjection
open CFSGFFourE6SignedFixedInclusion CFSGTwistedE6GeckRelativeRootGenerated
open CFSGFFourE6OriginalOppositeAlignment
open CFSGTwistedE6GeckRelativeOpposition CFSGConjugateSubgroupHomInjective
open CFSGSubgroupConjugateRestriction CFSGSerreQuadraticMatrix CFSG.Models.Chevalley

theorem signedFixedToOriginal_positive_apply (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)]
    (u : signedFixed K (RingEquiv.refl K) false) :
    signedFixedToOriginal K false u=fixedPositiveToOriginal K p u :=
  (fixedPositiveToOriginal_apply K p u).symm

def signedPart (K : Type) [Field K] (neg : Bool) :
    Subgroup (canonicalElementaryGroup realizationData K) :=
  (signedFixed K (RingEquiv.refl K) neg).subgroupOf (canonicalElementaryGroup realizationData K)

def oppositionInFolded (K : Type) [Field K] : canonicalElementaryGroup realizationData K :=
  ⟨relativeOpposition K,relativeOpposition_mem_folded K⟩

theorem signedPart_opposition (K : Type) [Field K] [Finite K] :
    (signedPart K false).map (MulAut.conj (oppositionInFolded K)).toMonoidHom=signedPart K true :=
  restrict_conjugate (canonicalElementaryGroup realizationData K) _ _
    (fun u hu=>fixedPositive_mem_folded K ⟨u,hu⟩)
    (fun u hu=>fixedNegative_mem_folded K ⟨u,hu⟩)
    (oppositionInFolded K) (fixed_positive_image_eq_fixed_negative K (RingEquiv.refl K))

private theorem positive_part_injective (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)] :
    Function.Injective ((foldedToOriginal K).comp (signedPart K false).subtype) := by
  intro a b he
  let ua : signedFixed K (RingEquiv.refl K) false := ⟨a.val.val,a.property⟩
  let ub : signedFixed K (RingEquiv.refl K) false := ⟨b.val.val,b.property⟩
  have ha : fixedPositiveToOriginal K p ua=foldedToOriginal K a.val :=
    fixedPositiveToOriginal_apply K p ua
  have hb : fixedPositiveToOriginal K p ub=foldedToOriginal K b.val :=
    fixedPositiveToOriginal_apply K p ub
  have hh := fixedPositiveToOriginal_injective K p (ha.trans (he.trans hb.symm))
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : signedFixed K (RingEquiv.refl K) false=>z.val) hh

theorem signedFixedToOriginal_injective (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)]
    (neg : Bool) : Function.Injective (signedFixedToOriginal K neg) := by
  cases neg
  · intro a b he
    apply fixedPositiveToOriginal_injective K p
    exact (signedFixedToOriginal_positive_apply K p a).symm.trans
      (he.trans (signedFixedToOriginal_positive_apply K p b))
  · have hi := injective_on_conjugate (foldedToOriginal K) (signedPart K false) (signedPart K true)
      (oppositionInFolded K) (signedPart_opposition K) (positive_part_injective K p)
    intro a b he
    let xa : signedPart K true := ⟨signedFixedToFolded K true a,a.property⟩
    let xb : signedPart K true := ⟨signedFixedToFolded K true b,b.property⟩
    have hh : xa=xb := hi he
    apply Subtype.ext
    exact congrArg (fun z : signedPart K true=>z.val.val) hh

end SymmetricSubgroupAsymptotics.CFSGFFourE6SignedOriginalProjection
