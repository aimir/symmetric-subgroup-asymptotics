import SymmetricSubgroupAsymptotics.TernaryFourAffineSymmetricTopClassBound

/-! An injective original source in the ternary four-coordinate wreath
product with full symmetric top has at most 330 classes. The exact affine
chart transports its actual image, never the full ambient group's count. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.TernaryFourWreathSymmetricTopClassBound
open TernaryWreathAffineSemidirectEquiv TernaryFourAffineProperKernelClassBound

theorem class_card_le_threeThirty {A : Type} [Group A] [Finite A]
    (f : A →* Wreath (Fin 4)) (hf : Function.Injective f)
    (ht : Function.Surjective
      ((PermutationalWreathProduct.rightHom : Wreath (Fin 4) →* Equiv.Perm (Fin 4)).comp f)) :
    Nat.card (ConjClasses A)≤330 := by
  let g : A →* Affine (Fin 4) := (equiv (Fin 4)).toMonoidHom.comp f
  have hg : Function.Injective g := (equiv (Fin 4)).injective.comp hf
  let e : A ≃* g.range := MulEquiv.ofBijective g.rangeRestrict
    ⟨fun _ _ h => hg (congrArg Subtype.val h),g.rangeRestrict_surjective⟩
  letI : Finite g.range := Finite.of_equiv A e.toEquiv
  have htop : Function.Surjective (originalTopHom g.range) := by
    intro s
    obtain ⟨x,hx⟩ := ht s
    refine ⟨⟨g x,⟨x,rfl⟩⟩,?_⟩
    change ((equiv (Fin 4)) (f x)).right.right=s
    exact (equiv_preserves_original_top (Fin 4) (f x)).trans hx
  rw [conjugacyClass_card_congr e]
  exact TernaryFourAffineSymmetricTopClassBound.class_card_le_threeThirty g.range htop

end SymmetricSubgroupAsymptotics.TernaryFourWreathSymmetricTopClassBound
