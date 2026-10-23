import SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedPositiveImageSylow

/-! The genuine fixed positive matrix group is isomorphic to the SAME
actual Sylow in the original derived action image. Injectivity uses the
proved positive action, without faithfulness of the full Lie source. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckPositiveDerivedEquiv
open CFSGTrialityGeckFixedPositiveImageSylow CFSGTrialityGeckDerivedSylowNormalizer
open CFSGTrialityGeckFixedPositiveGeneration CFSGTrialityGeckPositiveTwist
open CFSGTrialityGeckSourceWordAction CFSGSerreOrdinaryTwists

def positiveEquivSylow (q : CFSG.PrimePower) :
    fixedPositive (q.Extension 3) (definingFieldAutomorphism q 3) ≃* imagePositiveSylow q :=
  (preimagePositiveEquiv q).symm.trans
    ((MonoidHom.ofInjective (preimage_sylow_action_injective q)).trans
      (MulEquiv.subgroupCongr (imagePositiveSylow_range q).symm))

theorem positiveEquivSylow_action (q : CFSG.PrimePower)
    (u : fixedPositive (q.Extension 3) (definingFieldAutomorphism q 3)) :
    (positiveEquivSylow q u).val.val=positiveAction (q.Extension 3) u.val := by
  change (preimageToImage q ((preimagePositiveEquiv q).symm u).val).val=
    positiveAction (q.Extension 3) u.val
  rw [preimagePositiveEquiv_action]
  exact congrArg (fun z : fixedPositive (q.Extension 3) (definingFieldAutomorphism q 3)=>
    positiveAction (q.Extension 3) z.val) ((preimagePositiveEquiv q).apply_symm_apply u)

def positiveToDerived (q : CFSG.PrimePower) :
    fixedPositive (q.Extension 3) (definingFieldAutomorphism q 3) →* DerivedImage q :=
  (imagePositiveSylow q : Subgroup (DerivedImage q)).subtype.comp (positiveEquivSylow q).toMonoidHom

theorem positiveToDerived_injective (q : CFSG.PrimePower) :
    Function.Injective (positiveToDerived q) :=
  Subtype.val_injective.comp (positiveEquivSylow q).injective

theorem positiveToDerived_range (q : CFSG.PrimePower) :
    (positiveToDerived q).range=(imagePositiveSylow q : Subgroup (DerivedImage q)) := by
  ext x
  constructor
  · rintro ⟨u,rfl⟩
    exact (positiveEquivSylow q u).property
  · intro hx
    refine ⟨(positiveEquivSylow q).symm ⟨x,hx⟩,?_⟩
    exact congrArg (fun z : imagePositiveSylow q=>z.val)
      ((positiveEquivSylow q).apply_symm_apply ⟨x,hx⟩)

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckPositiveDerivedEquiv
