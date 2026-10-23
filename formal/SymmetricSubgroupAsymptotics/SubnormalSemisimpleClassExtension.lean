import SymmetricSubgroupAsymptotics.CFSGCompositionExtension
import SymmetricSubgroupAsymptotics.SubnormalCoordinateClassBound

/-! Class bounds across the actual intersection of a subnormal group
with a semisimple kernel. Kernel coordinates and quotient images are
retained literally; arbitrary subgroups of a simple factor are never
assigned the ambient factor's class bound. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.SubnormalSemisimpleClassExtension

theorem simple_subnormal_class_card_le {S : Type*} [Group S] [Finite S]
    [IsSimpleGroup S] (L : Subgroup S) (hL : L.IsSubnormal) :
    Nat.card (ConjClasses L) ≤ Nat.card (ConjClasses S) := by
  rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup inferInstance hL with hb | ht
  · subst L
    have hp : 1 ≤ Nat.card (ConjClasses S) := Nat.card_pos
    have hb : Nat.card (ConjClasses (⊥ : Subgroup S))=1 := by
      have hle := Nat.card_le_card_of_surjective (@ConjClasses.mk (⊥ : Subgroup S) _)
        ConjClasses.mk_surjective
      have hpos : 0 < Nat.card (ConjClasses (⊥ : Subgroup S)) := Nat.card_pos
      have hcard : Nat.card (⊥ : Subgroup S) = 1 := Nat.card_unique
      rw [hcard] at hle
      omega
    rw [hb]
    exact hp
  · subst L
    exact Nat.card_le_card_of_surjective
      (ConjClasses.map (Subgroup.topEquiv : (⊤ : Subgroup S) ≃* S).symm.toMonoidHom)
      (ConjClasses.map_surjective (Subgroup.topEquiv : (⊤ : Subgroup S) ≃* S).symm.surjective)

theorem subnormal_product_class_card_le (n : ℕ) (S : Fin n → Type*)
    [∀i,Group (S i)] [∀i,Finite (S i)] [∀i,IsSimpleGroup (S i)]
    (L : Subgroup (∀i,S i)) (hL : L.IsSubnormal) :
    Nat.card (ConjClasses L) ≤ ∏i,Nat.card (ConjClasses (S i)) := by
  let f (i : Fin n) : L →* S i := (Pi.evalMonoidHom S i).comp L.subtype
  have himage (i : Fin n) : (f i).range.IsSubnormal := by
    have hs : (L.map (Pi.evalMonoidHom S i)).IsSubnormal :=
      hL.map (fun x => ⟨Pi.mulSingle i x,Pi.mulSingle_eq_same i x⟩)
    simpa only [f,MonoidHom.range_comp,Subgroup.range_subtype] using hs
  apply SubnormalCoordinateClassBound.class_card_le_subnormal_coordinate_bounds
    n S (fun i => Nat.card (ConjClasses (S i))) f himage
    (fun _ M hM => simple_subnormal_class_card_le M hM)
  intro x y he
  apply Subtype.ext
  exact funext (fun i => congrFun he i)

variable {G Q : Type} [Group G] [Group Q] [Finite G]
    (f : G →* Q) (n : ℕ) (S : Fin n → Type)
    [∀i,Group (S i)] [∀i,Finite (S i)] [∀i,IsSimpleGroup (S i)]
    (e : f.ker ≃* ∀i,S i)

omit [Finite G] [∀i,Finite (S i)] in
theorem kernelCoordinates_eq_coordinate_product
    (hn : ∀i, ¬ IsMulCommutative (S i)) (H : Subgroup G) (hH : H.IsSubnormal) :
    CFSGCompositionExtension.kernelCoordinates f S e H =
      Subgroup.pi Set.univ (fun i =>
        (CFSGCompositionExtension.kernelCoordinates f S e H).map (Pi.evalMonoidHom S i)) :=
  CFSGSubnormalSimpleProduct.subnormal_eq_coordinate_product S hn _
    (CFSGCompositionExtension.kernelCoordinates_subnormal f S e H hH)

include e in
theorem subnormal_class_card_le_kernel_mul_range (H : Subgroup G) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H) ≤
      (∏i,Nat.card (ConjClasses (S i))) * Nat.card (ConjClasses (H.map f)) := by
  let fH : H →* Q := f.comp H.subtype
  let J := CFSGCompositionExtension.kernelCoordinates f S e H
  have hJ : J.IsSubnormal := CFSGCompositionExtension.kernelCoordinates_subnormal f S e H hH
  let a : fH.ker ≃* H.subgroupOf f.ker := {
    toFun := fun x => ⟨⟨x.val.val,x.property⟩,x.val.property⟩
    invFun := fun x => ⟨⟨x.val.val,x.property⟩,x.val.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_mul' := fun _ _ => rfl }
  let b : H.subgroupOf f.ker ≃* J := e.subgroupMap (H.subgroupOf f.ker)
  let c := a.trans b
  have hker : Nat.card (ConjClasses fH.ker) ≤ Nat.card (ConjClasses J) :=
    Nat.card_le_card_of_surjective (ConjClasses.map c.symm.toMonoidHom)
      (ConjClasses.map_surjective c.symm.surjective)
  have hrange : fH.range=H.map f := by
    dsimp only [fH]
    rw [MonoidHom.range_comp,Subgroup.range_subtype]
  have hs := conjugacyClass_card_le_kernel_mul_range fH
  rw [hrange] at hs
  exact hs.trans (Nat.mul_le_mul_right _
    (hker.trans (subnormal_product_class_card_le n S J hJ)))

include f e in
theorem subnormal_class_card_le_kernel_mul_card [Finite Q]
    (H : Subgroup G) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H) ≤ (∏i,Nat.card (ConjClasses (S i))) * Nat.card Q := by
  have hQ : Nat.card (ConjClasses (H.map f)) ≤ Nat.card Q :=
    (Nat.card_le_card_of_surjective (@ConjClasses.mk (H.map f) _)
      ConjClasses.mk_surjective).trans (H.map f).card_le_card_group
  exact (subnormal_class_card_le_kernel_mul_range f n S e H hH).trans
    (Nat.mul_le_mul_left _ hQ)

end SymmetricSubgroupAsymptotics.SubnormalSemisimpleClassExtension
