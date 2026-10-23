import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckGeneratedOppositeAlignment
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckFixedPositiveProjection
import SymmetricSubgroupAsymptotics.CFSGQuotientOppositeAlignment

/-! Actual opposite alignment descends to the SAME original simple
twisted E6 model through the checked surjection from J. Only the genuine
positive subgroup restriction is injective; no original automorphism
is lifted and no faithfulness of the whole matrix action is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalOppositeAlignment
open CFSGTwistedE6GeckGeneratedOppositeAlignment CFSGTwistedE6GeckFixedPositiveProjection
open CFSGTwistedE6GeckOriginalProjection CFSGTwistedE6GeckImagePositiveSylow
open CFSGTwistedE6GeckRelativeRootGenerated CFSGTwistedE6GeckRootGeneratedPGroup
open CFSGTwistedE6GeckGeneratedActionImage CFSGTwistedE6OriginalGoodSylow
open CFSGTwistedE6FixedA2 CFSGSerreOrdinaryTwists CFSGQuotientOppositeAlignment

def signedFixedToGenerated (q : CFSG.PrimePower) (neg : Bool) :
    signedFixed (q.Extension 2) (definingFieldAutomorphism q 2) neg→*
      fixedRootGenerated (q.Extension 2) (definingFieldAutomorphism q 2) :=
  Subgroup.inclusion (signedFixed_le_generated (q.Extension 2) (definingFieldAutomorphism q 2) neg)

def signedFixedToOriginal (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.TwistedE6 q)]
    (neg : Bool) : signedFixed (q.Extension 2) (definingFieldAutomorphism q 2) neg→*
      CFSG.Models.TwistedE6 q :=
  (generatedToOriginal q).comp (signedFixedToGenerated q neg)

theorem signedFixedToOriginal_positive (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] :
    signedFixedToOriginal q false=fixedPositiveToOriginal q := rfl

def originalNegative (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.TwistedE6 q)] :
    Subgroup (CFSG.Models.TwistedE6 q) :=
  (rootPart (q.Extension 2) (definingFieldAutomorphism q 2) true).map (generatedToOriginal q)

theorem rootPart_positive_original_image (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] :
    (rootPart (q.Extension 2) (definingFieldAutomorphism q 2) false).map (generatedToOriginal q)=
      (originalPositiveSylow q : Subgroup (CFSG.Models.TwistedE6 q)) := by
  change (rootPart (q.Extension 2) (definingFieldAutomorphism q 2) false).map
    ((imageToOriginal q).comp (generatedToDerived q))=
      (imagePositiveSylow q : Subgroup (derivedImageAction q).range).map (imageToOriginal q)
  rw [←Subgroup.map_map,←imagePositiveSylow_coe]

theorem rootPart_positive_original_injective (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] :
    Function.Injective ((generatedToOriginal q).comp
      (rootPart (q.Extension 2) (definingFieldAutomorphism q 2) false).subtype) := by
  intro x y he
  let ux : signedFixed (q.Extension 2) (definingFieldAutomorphism q 2) false :=
    ⟨x.val.val,x.property⟩
  let uy : signedFixed (q.Extension 2) (definingFieldAutomorphism q 2) false :=
    ⟨y.val.val,y.property⟩
  have he' : fixedPositiveToOriginal q ux=fixedPositiveToOriginal q uy := he
  have hu := fixedPositiveToOriginal_injective q he'
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun u : signedFixed (q.Extension 2) (definingFieldAutomorphism q 2) false=>u.val) hu

theorem original_opposite_conjugate_by_positive (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] (g : CFSG.Models.TwistedE6 q)
    (hdisj : (originalPositiveSylow q : Subgroup (CFSG.Models.TwistedE6 q))⊓
      (originalPositiveSylow q : Subgroup (CFSG.Models.TwistedE6 q)).map
        (MulAut.conj g).toMonoidHom=⊥) :
    ∃b∈(originalPositiveSylow q : Subgroup (CFSG.Models.TwistedE6 q)),
      (originalPositiveSylow q : Subgroup (CFSG.Models.TwistedE6 q)).map
        (MulAut.conj g).toMonoidHom=(originalNegative q).map (MulAut.conj b).toMonoidHom := by
  have h := opposite_alignment_map (generatedToOriginal q) (generatedToOriginal_surjective q)
    (rootPart (q.Extension 2) (definingFieldAutomorphism q 2) false)
    (rootPart (q.Extension 2) (definingFieldAutomorphism q 2) true)
    (rootPart (q.Extension 2) (definingFieldAutomorphism q 2) false)
    (rootPart_positive_original_injective q)
    (generated_opposite_conjugate_by_positive (q.Extension 2) (definingFieldAutomorphism q 2)) g
  rw [rootPart_positive_original_image] at h
  exact h hdisj

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalOppositeAlignment
