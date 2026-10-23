import SymmetricSubgroupAsymptotics.BinaryBlockWreathCodimension

/-! Saturating the actual binary kernel identifies the ORIGINAL group
with the full binary wreath product with its SAME literal top. This is
an actual group equivalence, not a comparison with an enlarged base. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryBlockWreathSaturation
open OriginalBlockClassBound BinaryBlockWreathCodimension

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [MulAction.IsPretransitive A X] [FaithfulSMul A Ω]
    [Finite A] [Finite Ω] [Finite X]
    (b : Ω → X) (hb : ∀ (a : A) (ω : Ω),b (a • ω)=a • b ω) (x0 : X)
    (htwo : Nat.card (originalBlockFibre b x0)=2)
    (hfull : Nat.card (Kernel (A := A) (X := X))=2^Nat.card X)

omit [Finite A] in
include htwo hfull in
theorem fullEmbedding_surjective : Function.Surjective (fullEmbedding b hb x0) := by
  have hi := kernel_mul_embedding_index b hb x0 htwo
  rw [hfull] at hi
  have he : 2^Nat.card X * (fullEmbedding b hb x0).range.index=
      2^Nat.card X * 1 := by simpa only [Nat.mul_one] using hi
  have hp : 0<(2:ℕ)^Nat.card X := pow_pos (by decide) _
  have hindex : (fullEmbedding b hb x0).range.index=1 :=
    Nat.le_antisymm (Nat.le_of_mul_le_mul_left he.le hp)
      (Nat.le_of_mul_le_mul_left he.ge hp)
  exact MonoidHom.range_eq_top.mp (Subgroup.index_eq_one.mp hindex)

def fullWreathEquiv : A ≃* FullWreath (A := A) b x0 :=
  MulEquiv.ofBijective (fullEmbedding b hb x0)
    ⟨fullEmbedding_injective b hb x0,fullEmbedding_surjective b hb x0 htwo hfull⟩

include hb htwo hfull in
theorem class_card_eq_fullWreath :
    Nat.card (ConjClasses A)=Nat.card (ConjClasses (FullWreath (A := A) b x0)) := by
  let e := fullWreathEquiv b hb x0 htwo hfull
  apply Nat.le_antisymm
  · exact Nat.card_le_card_of_surjective (ConjClasses.map e.symm.toMonoidHom)
      (ConjClasses.map_surjective e.symm.surjective)
  · exact Nat.card_le_card_of_surjective (ConjClasses.map e.toMonoidHom)
      (ConjClasses.map_surjective e.surjective)

end SymmetricSubgroupAsymptotics.BinaryBlockWreathSaturation
