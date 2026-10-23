import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalProjection

/-! The literal semilinear fixed upper matrices are in bijection with
the named Sylow of the SAME original Derived image. Their actual map to
the original projective model is injective and has the strict square
order margin needed for symbolic-unipotent root-family counting. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckFixedPositiveProjection
open CFSGTwistedE6GeckOriginalProjection CFSGTwistedE6GeckImagePositiveSylow
open CFSGTwistedE6GeckProjectiveSylowOrder CFSGTwistedE6OriginalGoodSylow
open CFSGTwistedE6GeckRelativeRootGenerated CFSGTwistedE6GeckRootGeneratedPGroup
open CFSGTwistedE6GeckPositiveTwist CFSGTwistedE6GeckPositiveActionInjective
open CFSGTwistedE6GeckSourceAction CFSGTwistedE6FixedA2 CFSGSerreOrdinaryTwists
local instance (q : CFSG.PrimePower) : Fact q.prime.Prime := ⟨q.prime_isPrime⟩

def fixedPositiveToGenerated (q : CFSG.PrimePower) :
    signedFixed (q.Extension 2) (definingFieldAutomorphism q 2) false→*
      fixedRootGenerated (q.Extension 2) (definingFieldAutomorphism q 2) :=
  Subgroup.inclusion (signedFixed_le_generated (q.Extension 2) (definingFieldAutomorphism q 2) false)

def fixedPositiveToImage (q : CFSG.PrimePower) :
    signedFixed (q.Extension 2) (definingFieldAutomorphism q 2) false→*imagePositiveSylow q :=
  ((generatedToDerived q).comp (fixedPositiveToGenerated q)).codRestrict
    (imagePositiveSylow q : Subgroup (derivedImageAction q).range) (fun u=>by
      change generatedToDerived q (fixedPositiveToGenerated q u)∈
        (imagePositiveSylow q : Subgroup (derivedImageAction q).range)
      rw [imagePositiveSylow_coe]
      exact ⟨fixedPositiveToGenerated q u,u.property,rfl⟩)

theorem fixedPositiveToImage_injective (q : CFSG.PrimePower) :
    Function.Injective (fixedPositiveToImage q) := by
  intro u v he
  have hh := congrArg (fun z : imagePositiveSylow q=>z.val.val) he
  have hact : positiveAction (q.Extension 2) ⟨u.val,u.property.1⟩=
      positiveAction (q.Extension 2) ⟨v.val,v.property.1⟩ := hh
  have hunit := congrArg (fun z : Positive (q.Extension 2)=>z.val)
    (positiveAction_injective (q.Extension 2) q.prime hact)
  exact Subtype.ext hunit

theorem fixedPositiveToImage_surjective (q : CFSG.PrimePower) :
    Function.Surjective (fixedPositiveToImage q) := by
  intro y
  have hy : y.val∈(rootPart (q.Extension 2) (definingFieldAutomorphism q 2) false).map
      (generatedToDerived q) := by
    rw [←imagePositiveSylow_coe]
    exact y.property
  obtain ⟨j,hj,he⟩ := hy
  exact ⟨⟨j.val,hj⟩,Subtype.ext he⟩

def fixedPositiveImageEquiv (q : CFSG.PrimePower) :
    signedFixed (q.Extension 2) (definingFieldAutomorphism q 2) false≃*imagePositiveSylow q :=
  MulEquiv.ofBijective (fixedPositiveToImage q)
    ⟨fixedPositiveToImage_injective q,fixedPositiveToImage_surjective q⟩

theorem fixedPositive_card (q : CFSG.PrimePower) :
    Nat.card (signedFixed (q.Extension 2) (definingFieldAutomorphism q 2) false)=
      Nat.card (imagePositiveSylow q) := Nat.card_congr (fixedPositiveImageEquiv q).toEquiv

def fixedPositiveToOriginal (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.TwistedE6 q)] :
    signedFixed (q.Extension 2) (definingFieldAutomorphism q 2) false→*CFSG.Models.TwistedE6 q :=
  (positiveToOriginal q).comp (fixedPositiveToImage q)

theorem fixedPositiveToOriginal_injective (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] : Function.Injective (fixedPositiveToOriginal q) :=
  (positiveToOriginal_injective q).comp (fixedPositiveToImage_injective q)

theorem fixedPositive_square_lt_original_order (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] :
    Nat.card (signedFixed (q.Extension 2) (definingFieldAutomorphism q 2) false)^2<
      Nat.card (CFSG.Models.TwistedE6 q) := by
  rw [fixedPositive_card]
  exact original_positive_sylow_square_lt_order q

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckFixedPositiveProjection
