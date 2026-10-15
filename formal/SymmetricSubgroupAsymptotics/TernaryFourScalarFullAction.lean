import SymmetricSubgroupAsymptotics.TernaryFourScalarFullProjection

/-! The original twelve-point action of a full scalar four-block module.
Even block lifts with scalar one recover every translation from one actual
coordinate translation, using the checked invariant-submodule lattice. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics.TernaryFourScalarFullAction

open SemidirectProduct TernaryFourFullModuleCoordinates

variable {R : Type} [Group R]
variable (b : R →* Equiv.Perm (Fin 4)) (s : R →* (ZMod 3)ˣ)

abbrev Model := TernaryFourScalarFullProjection.Model b s

def action : Model b s →* Equiv.Perm (Fin 12) :=
  TernaryFourAugmentationAffineImage.pointEquiv.symm.permCongrHom.toMonoidHom.comp
    (TernaryMonomialSemidirect.action b s)

theorem action_inl (v : Multiplicative FullVector) :
    action b s (inl v) = translation v := by
  simp only [action,translation,pointAction,MonoidHom.comp_apply,
    TernaryMonomialSemidirect.action,SemidirectProduct.lift_inl]

theorem action_inr (r : R) :
    action b s (inr r) = TernaryFourScalarAugmentation.blockPerm b s r := by
  simp only [action,TernaryFourScalarAugmentation.blockPerm,MonoidHom.comp_apply,
    TernaryMonomialSemidirect.action,SemidirectProduct.lift_inr]

theorem blockPerm_of_scalar_one (r : R) (hr : s r = 1) :
    TernaryFourScalarAugmentation.blockPerm b s r =
      TernaryFourAugmentationAffineImage.blockPerm (b r) := by
  apply congrArg TernaryFourAugmentationAffineImage.pointEquiv.symm.permCongrHom.toMonoidHom
  apply Equiv.ext
  intro p
  apply Prod.ext
  · rfl
  · change (s r : ZMod 3) * p.2 = (1 : ZMod 3) * p.2
    simp only [hr,Units.val_one]

theorem all_translations_mem (H : Subgroup (Equiv.Perm (Fin 12)))
    (heven : ∀ g : alternatingGroup (Fin 4), ∃ r : R, b r = g.1 ∧ s r = 1)
    (hblocks : ∀ r : R, TernaryFourScalarAugmentation.blockPerm b s r ∈ H)
    (hseed : translation (Multiplicative.ofAdd unitSeed) ∈ H)
    (v : Multiplicative FullVector) : translation v ∈ H := by
  apply full_translation_mem H _ hseed v
  intro g hg
  obtain ⟨r,hb,hs⟩ := heven ⟨g,hg⟩
  change b r = g at hb
  rw [← hb,← blockPerm_of_scalar_one b s r hs]
  exact hblocks r

theorem action_range_le (H : Subgroup (Equiv.Perm (Fin 12)))
    (ht : ∀ v : Multiplicative FullVector, translation v ∈ H)
    (hb : ∀ r : R, TernaryFourScalarAugmentation.blockPerm b s r ∈ H) :
    (action b s).range ≤ H := by
  rintro _ ⟨g,rfl⟩
  rw [← inl_left_mul_inr_right g,map_mul,action_inl,action_inr]
  exact H.mul_mem (ht g.left) (hb g.right)

end SymmetricSubgroupAsymptotics.TernaryFourScalarFullAction

end
