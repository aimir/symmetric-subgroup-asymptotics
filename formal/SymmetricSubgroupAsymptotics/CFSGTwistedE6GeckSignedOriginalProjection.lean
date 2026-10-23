import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalOppositeAlignment
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckRelativeOpposition
import SymmetricSubgroupAsymptotics.CFSGConjugateSubgroupHomInjective
import SymmetricSubgroupAsymptotics.CFSGSubgroupConjugateRestriction

/-! Both actual fixed signed upper subgroups inject into the ORIGINAL
twisted E6 model. The negative restriction is transported by the actual
relative opposition word from the proved positive restriction; no claim
of global source or action-map faithfulness is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckSignedOriginalProjection
open CFSGTwistedE6GeckOriginalProjection CFSGTwistedE6GeckFixedPositiveProjection
open CFSGTwistedE6GeckOriginalOppositeAlignment
open CFSGTwistedE6GeckRelativeRootGenerated CFSGTwistedE6GeckRootGeneratedPGroup
open CFSGTwistedE6GeckRelativeOpposition CFSGTwistedE6GeckProjectiveSylowOrder
open CFSGConjugateSubgroupHomInjective CFSGSubgroupConjugateRestriction CFSGSerreOrdinaryTwists

theorem rootPart_opposition (q : CFSG.PrimePower) :
    (rootPart (q.Extension 2) (definingFieldAutomorphism q 2) false).map
      (MulAut.conj (oppositionInGenerated q)).toMonoidHom=
        rootPart (q.Extension 2) (definingFieldAutomorphism q 2) true :=
  restrict_conjugate (fixedRootGenerated (q.Extension 2) (definingFieldAutomorphism q 2)) _ _
    (signedFixed_le_generated (q.Extension 2) (definingFieldAutomorphism q 2) false)
    (signedFixed_le_generated (q.Extension 2) (definingFieldAutomorphism q 2) true)
    (oppositionInGenerated q)
    (fixed_positive_image_eq_fixed_negative (q.Extension 2) (definingFieldAutomorphism q 2))

theorem signedFixedToOriginal_injective (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] (neg : Bool) :
    Function.Injective (signedFixedToOriginal q neg) := by
  cases neg
  · rw [signedFixedToOriginal_positive]
    exact fixedPositiveToOriginal_injective q
  · have hi := injective_on_conjugate (generatedToOriginal q)
      (rootPart (q.Extension 2) (definingFieldAutomorphism q 2) false)
      (rootPart (q.Extension 2) (definingFieldAutomorphism q 2) true)
      (oppositionInGenerated q) (rootPart_opposition q) (rootPart_positive_original_injective q)
    intro a b he
    let xa : rootPart (q.Extension 2) (definingFieldAutomorphism q 2) true :=
      ⟨signedFixedToGenerated q true a,a.property⟩
    let xb : rootPart (q.Extension 2) (definingFieldAutomorphism q 2) true :=
      ⟨signedFixedToGenerated q true b,b.property⟩
    have hh : xa=xb := hi he
    apply Subtype.ext
    exact congrArg (fun z : rootPart (q.Extension 2) (definingFieldAutomorphism q 2) true=>z.val.val) hh

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckSignedOriginalProjection
