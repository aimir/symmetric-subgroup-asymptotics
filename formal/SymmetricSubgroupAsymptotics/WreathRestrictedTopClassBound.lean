import SymmetricSubgroupAsymptotics.PermutationalWreathFinite
import SymmetricSubgroupAsymptotics.ConjugacyClassExtension
import Mathlib.GroupTheory.Index

/-! Restricting the top of the full wreath product identifies an actual
preimage subgroup. A normal top subgroup therefore gives an extension
class bound, without any monotonicity comparison of subgroups. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.WreathRestrictedTopClassBound

variable {C Q I : Type} [Group C] [Group Q] [MulAction Q I]

def topPreimageEquiv (R : Subgroup Q) :
    PermutationalWreathProduct C R I ≃*
      R.comap (PermutationalWreathProduct.rightHom (D := C) (I := I)) where
  toFun w := ⟨⟨w.left,w.right.val⟩,w.right.property⟩
  invFun w := ⟨w.val.left,⟨w.val.right,w.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' a b := by
    apply Subtype.ext
    apply PermutationalWreathProduct.ext <;> rfl

theorem topPreimage_index (R : Subgroup Q) :
    (R.comap (PermutationalWreathProduct.rightHom (D := C) (I := I))).index =
      R.index := by
  apply R.index_comap_of_surjective
  intro q
  exact ⟨PermutationalWreathProduct.topHom q,rfl⟩

theorem class_card_le_restricted_mul_index [Finite C] [Finite Q] [Finite I]
    (R : Subgroup Q) [R.Normal] :
    Nat.card (ConjClasses (PermutationalWreathProduct C Q I)) ≤
      Nat.card (ConjClasses (PermutationalWreathProduct C R I)) * R.index := by
  let N := R.comap (PermutationalWreathProduct.rightHom (D := C) (I := I))
  letI : N.Normal := inferInstance
  have hq : Nat.card (ConjClasses (PermutationalWreathProduct C Q I ⧸ N)) ≤ N.index :=
    Nat.card_le_card_of_surjective _ ConjClasses.mk_surjective
  let e := topPreimageEquiv (C := C) (I := I) R
  have he : Nat.card (ConjClasses N) ≤
      Nat.card (ConjClasses (PermutationalWreathProduct C R I)) :=
    Nat.card_le_card_of_surjective (ConjClasses.map e.toMonoidHom)
      (ConjClasses.map_surjective e.surjective)
  have hi : N.index = R.index := topPreimage_index R
  exact (conjugacyClass_card_le_normal_mul_quotient N).trans
    ((Nat.mul_le_mul he hq).trans_eq (congrArg (fun n =>
      Nat.card (ConjClasses (PermutationalWreathProduct C R I)) * n) hi))

end SymmetricSubgroupAsymptotics.WreathRestrictedTopClassBound
