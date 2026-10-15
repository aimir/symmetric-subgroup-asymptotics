import SymmetricSubgroupAsymptotics.TernaryFourScalarFullAction

/-! Actual diagonal affine cocycles on the four-block augmentation model.
The complement may carry translations. Its displayed cocycle law, not
an assertion that the original generators split, defines the image map. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics.TernaryFourCocycleImages

open SemidirectProduct TernaryFourAugmentationRepresentation

variable {R : Type} [Group R]

structure Cocycle (s : R →* (ZMod 3)ˣ) where
  value : R → ZMod 3
  one : value 1 = 0
  mul : ∀ g h, value (g*h) = value g + (s g : ZMod 3)*value h

variable (b : R →* Equiv.Perm (Fin 4)) (s : R →* (ZMod 3)ˣ) (d : Cocycle s)

def complementLift : R →* TernaryMonomialSemidirect.Model b s where
  toFun r := ⟨Multiplicative.ofAdd (fun _ => d.value r),r⟩
  map_one' := by
    apply SemidirectProduct.ext
    · apply Multiplicative.toAdd.injective
      funext i
      exact d.one
    · rfl
  map_mul' g h := by
    apply SemidirectProduct.ext
    · apply Multiplicative.toAdd.injective
      funext i
      exact d.mul g h
    · rfl

def fullMap : TernaryFourScalarAugmentation.Model b s →*
    TernaryMonomialSemidirect.Model b s :=
  SemidirectProduct.lift
    (inl.comp encodeLinear.toAddMonoidHom.toMultiplicative)
    (complementLift b s d) (by
      intro r
      apply MonoidHom.ext
      intro v
      change inl (Multiplicative.ofAdd (encode (TernaryFourScalarAugmentation.linearHom b s r v.toAdd))) =
        complementLift b s d r * inl (Multiplicative.ofAdd (encode v.toAdd)) *
          (complementLift b s d r)⁻¹
      rw [LinearSemidirectCoprimeSocleBounds.conjugate_translation]
      apply congrArg inl
      apply Multiplicative.toAdd.injective
      change encode (TernaryFourScalarAugmentation.linearHom b s r v.toAdd) =
        fun i => (s r : ZMod 3) * encode v.toAdd (b r⁻¹ i)
      rw [b.map_inv]
      exact TernaryFourScalarAugmentation.encode_linearHom b s r v.toAdd)

def action : TernaryFourScalarAugmentation.Model b s →* Equiv.Perm (Fin 12) :=
  (TernaryFourScalarFullAction.action b s).comp (fullMap b s d)

def complementAction : R →* Equiv.Perm (Fin 12) :=
  (TernaryFourScalarFullAction.action b s).comp (complementLift b s d)

theorem action_inl (v : Multiplicative Vector) :
    action b s d (inl v) = TernaryFourAugmentationAffineImage.translationPerm v := by
  simp only [action,fullMap,MonoidHom.comp_apply,SemidirectProduct.lift_inl]
  rw [TernaryFourScalarFullAction.action_inl]
  exact TernaryFourFullModuleCoordinates.augmentation_translation v

theorem action_inr (r : R) : action b s d (inr r) = complementAction b s d r := by
  simp only [action,fullMap,complementAction,MonoidHom.comp_apply,SemidirectProduct.lift_inr]

theorem complementAction_apply (r : R) (x : Fin 12) :
    TernaryFourAugmentationAffineImage.pointEquiv (complementAction b s d r x) =
      (b r (TernaryFourAugmentationAffineImage.pointEquiv x).1,
       d.value r + (s r : ZMod 3)*(TernaryFourAugmentationAffineImage.pointEquiv x).2) := by
  change TernaryFourAugmentationAffineImage.pointEquiv
    (TernaryFourAugmentationAffineImage.pointEquiv.symm
      (b r (TernaryFourAugmentationAffineImage.pointEquiv x).1,
       d.value r + (s r : ZMod 3)*(TernaryFourAugmentationAffineImage.pointEquiv x).2)) = _
  exact TernaryFourAugmentationAffineImage.pointEquiv.apply_symm_apply _

end SymmetricSubgroupAsymptotics.TernaryFourCocycleImages

end
