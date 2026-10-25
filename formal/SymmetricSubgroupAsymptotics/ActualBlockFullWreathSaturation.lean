import SymmetricSubgroupAsymptotics.ActualBlockWreathEmbedding
import SymmetricSubgroupAsymptotics.WreathFullBaseSaturation
import SymmetricSubgroupAsymptotics.BlockKernelClassBound

/-! Saturation for the literal original block embedding and SAME top.
The full-base cardinal equality yields an actual group equivalence to
the full wreath product. No class comparison for a proper base occurs. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ActualBlockFullWreathSaturation
open OriginalBlockClassBound ActualBlockWreathEmbedding

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [MulAction.IsPretransitive A X] [FaithfulSMul A Ω]
    [Finite A] [Finite Ω] [Finite X]
    (b : Ω → X) (hb : ∀ (a : A) (ω : Ω), b (a • ω) = a • b ω) (x0 : X)

theorem right_kernel_eq :
    (PermutationalWreathProduct.rightHom.comp (embedding b hb x0)).ker =
      Kernel (A := A) (X := X) := by
  ext a
  change (embedding b hb x0 a).right = 1 ↔ OriginalBlockClassBound.topMap (A := A) (X := X) a = 1
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

theorem right_surjective :
    Function.Surjective (PermutationalWreathProduct.rightHom.comp (embedding b hb x0)) := by
  change Function.Surjective (OriginalBlockClassBound.topMap (A := A) (X := X)).rangeRestrict
  exact (OriginalBlockClassBound.topMap (A := A) (X := X)).rangeRestrict_surjective

theorem embedding_surjective_of_kernel_card
    (hfull : Nat.card (Kernel (A := A) (X := X)) =
      Nat.card (originalBlockComponent b hb x0) ^ Nat.card X) :
    Function.Surjective (embedding b hb x0) := by
  apply WreathFullBaseSaturation.surjective_of_kernel_card (embedding b hb x0)
    (embedding_injective b hb x0) (right_surjective b hb x0)
  rw [right_kernel_eq b hb x0]
  exact hfull

def fullWreathEquiv
    (hfull : Nat.card (Kernel (A := A) (X := X)) =
      Nat.card (originalBlockComponent b hb x0) ^ Nat.card X) :
    A ≃* PermutationalWreathProduct (originalBlockComponent b hb x0)
      (OriginalBlockClassBound.Top (A := A) (X := X)) X :=
  MulEquiv.ofBijective (embedding b hb x0)
    ⟨embedding_injective b hb x0,embedding_surjective_of_kernel_card b hb x0 hfull⟩

theorem class_card_eq_fullWreath
    (hfull : Nat.card (Kernel (A := A) (X := X)) =
      Nat.card (originalBlockComponent b hb x0) ^ Nat.card X) :
    Nat.card (ConjClasses A) = Nat.card (ConjClasses
      (PermutationalWreathProduct (originalBlockComponent b hb x0)
        (OriginalBlockClassBound.Top (A := A) (X := X)) X)) := by
  let e := fullWreathEquiv b hb x0 hfull
  apply Nat.le_antisymm
  · exact Nat.card_le_card_of_surjective (ConjClasses.map e.symm.toMonoidHom)
      (ConjClasses.map_surjective e.symm.surjective)
  · exact Nat.card_le_card_of_surjective (ConjClasses.map e.toMonoidHom)
      (ConjClasses.map_surjective e.surjective)

end SymmetricSubgroupAsymptotics.ActualBlockFullWreathSaturation
