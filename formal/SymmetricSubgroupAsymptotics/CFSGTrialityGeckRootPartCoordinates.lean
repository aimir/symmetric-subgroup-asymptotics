import SymmetricSubgroupAsymptotics.CFSGTrialityGeckRootGeneratedPGroup
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckPositiveDerivedEquiv
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckGoodSylow

/-! The positive part of literal J has exactly the genuine fixed
positive coordinates. Its action maps onto the SAME named positive
Sylow in the original derived image. No whole-action injectivity is used. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckRootPartCoordinates
open CFSGTrialityGeckRootGeneratedPGroup CFSGTrialityGeckRelativeRootGenerated
open CFSGTrialityGeckFixedPositiveGeneration CFSGTrialityGeckPositiveTwist
open CFSGTrialityGeckMatrixTwist CFSGTrialityGeckSourceWordAction
open CFSGTrialityGeckPositiveDerivedEquiv CFSGTrialityGeckFixedPositiveImageSylow
open CFSGTrialityGeckGoodSylow CFSGTrialityGeckDerivedRootGeneration
open CFSGSerreOrdinaryTwists

def positivePartEquiv (K : Type) [Field K] [Finite K] (sigma : K ≃+* K) :
    rootPart K sigma false ≃* fixedPositive K sigma where
  toFun x := ⟨⟨x.val.val,x.property.1⟩,Subtype.ext x.property.2⟩
  invFun u := by
    have hf : unitTwist K sigma u.val.val = u.val.val := by
      have he := congrArg (fun z : Positive K => z.val) u.property
      change (positiveTwist K sigma u.val).val = u.val.val at he
      rw [positiveTwist_val] at he
      exact he
    have hu : u.val.val ∈ signedFixed K sigma false := ⟨u.val.property,hf⟩
    exact ⟨⟨u.val.val,signedFixed_le_generated K sigma false hu⟩,hu⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem positivePartEquiv_action (K : Type) [Field K] [Finite K] (sigma : K ≃+* K)
    (x : rootPart K sigma false) :
    generatedAction K sigma x.val = positiveAction K (positivePartEquiv K sigma x).val := rfl

theorem positivePart_derived_action (q : CFSG.PrimePower)
    (x : rootPart (q.Extension 3) (definingFieldAutomorphism q 3) false) :
    generatedToDerived q x.val = positiveToDerived q
      (positivePartEquiv (q.Extension 3) (definingFieldAutomorphism q 3) x) := by
  apply Subtype.ext
  change generatedAction (q.Extension 3) (definingFieldAutomorphism q 3) x.val = _
  rw [positivePartEquiv_action]
  exact (positiveEquivSylow_action q _).symm

theorem positivePart_derived_image (q : CFSG.PrimePower) :
    (rootPart (q.Extension 3) (definingFieldAutomorphism q 3) false).map
      (generatedToDerived q) = (imagePositiveSylow q : Subgroup (DerivedImage q)) := by
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    have he := positivePart_derived_action q ⟨x,hx⟩
    rw [he]
    exact (positiveEquivSylow q _).property
  · intro a ha
    have hr : a ∈ (positiveToDerived q).range := by
      rw [positiveToDerived_range]
      exact ha
    obtain ⟨u,rfl⟩ := hr
    let x := (positivePartEquiv (q.Extension 3) (definingFieldAutomorphism q 3)).symm u
    refine ⟨x.val,x.property,?_⟩
    exact (positivePart_derived_action q x).trans
      (congrArg (positiveToDerived q)
        ((positivePartEquiv (q.Extension 3) (definingFieldAutomorphism q 3)).apply_symm_apply u))

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckRootPartCoordinates
