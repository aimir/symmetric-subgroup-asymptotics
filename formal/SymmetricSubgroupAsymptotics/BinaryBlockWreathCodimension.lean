import SymmetricSubgroupAsymptotics.ActualBlockWreathEmbedding
import SymmetricSubgroupAsymptotics.PermutationalWreathQuotient
import SymmetricSubgroupAsymptotics.PermutationalWreathFinite
import SymmetricSubgroupAsymptotics.BlockKernelClassBound
import SymmetricSubgroupAsymptotics.ConjugacyClassSubgroupIndexBound
import Mathlib.Data.Finite.Perm
import Mathlib.Data.Nat.Prime.Basic

/-! The full binary codimension of an ORIGINAL faithful block action.
The original group embeds into the full wreath product with its SAME top.
The image index is 2^d, and the original kernel has order 2^(b-d).
Both class bounds retain d; no subgroup class monotonicity is used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryBlockWreathCodimension
open OriginalBlockClassBound

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [MulAction.IsPretransitive A X] [FaithfulSMul A Ω]
    (b : Ω → X) (hb : ∀ (a : A) (ω : Ω),b (a • ω)=a • b ω) (x0 : X)

abbrev FullWreath := PermutationalWreathProduct
  (Equiv.Perm (originalBlockFibre b x0)) (Top (A := A) (X := X)) X

def fullEmbedding : A →* FullWreath (A := A) b x0 :=
  (PermutationalWreathProduct.mapBase
    (originalBlockComponent b hb x0).subtype).comp
      (ActualBlockWreathEmbedding.embedding b hb x0)

theorem fullEmbedding_injective : Function.Injective (fullEmbedding b hb x0) := by
  intro a c he
  apply ActualBlockWreathEmbedding.embedding_injective b hb x0
  apply PermutationalWreathProduct.ext
  · funext x
    apply Subtype.ext
    exact congrArg (fun w : FullWreath (A := A) b x0 => w.left x) he
  · exact congrArg (fun w : FullWreath (A := A) b x0 => w.right) he

variable [Finite A] [Finite Ω] [Finite X]

omit [MulAction A Ω] [MulAction.IsPretransitive A X] [FaithfulSMul A Ω] [Finite A] in
theorem fullWreath_card (htwo : Nat.card (originalBlockFibre b x0)=2) :
    Nat.card (FullWreath (A := A) b x0)=
      2^Nat.card X * Nat.card (Top (A := A) (X := X)) := by
  rw [PermutationalWreathProduct.natCard_eq,Nat.card_perm,htwo]
  rfl

omit [MulAction.IsPretransitive A X] [Finite A] [Finite X] in
theorem kernel_mul_top_card :
    Nat.card (Kernel (A := A) (X := X)) *
      Nat.card (Top (A := A) (X := X))=Nat.card A := by
  have h := (topMap (A := A) (X := X)).ker.card_mul_index
  rw [Subgroup.index_ker] at h
  exact h

private theorem cancel_positive_right {a b c : ℕ} (hc : 0<c)
    (h : a*c=b*c) : a=b :=
  Nat.le_antisymm (Nat.le_of_mul_le_mul_right h.le hc)
    (Nat.le_of_mul_le_mul_right h.ge hc)

omit [Finite A] in
theorem kernel_mul_embedding_index
    (htwo : Nat.card (originalBlockFibre b x0)=2) :
    Nat.card (Kernel (A := A) (X := X)) * (fullEmbedding b hb x0).range.index=
      2^Nat.card X := by
  have hcard : Nat.card (fullEmbedding b hb x0).range=Nat.card A :=
    (Nat.card_congr (MonoidHom.ofInjective
      (fullEmbedding_injective b hb x0)).toEquiv).symm
  have h := (fullEmbedding b hb x0).range.card_mul_index
  rw [hcard,← kernel_mul_top_card (A := A) (X := X),fullWreath_card b x0 htwo] at h
  apply cancel_positive_right (Nat.card_pos (α := Top (A := A) (X := X)))
  simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using h

theorem exists_codimension (htwo : Nat.card (originalBlockFibre b x0)=2) :
    ∃ d≤Nat.card X,
      (fullEmbedding b hb x0).range.index=2^d ∧
      Nat.card (Kernel (A := A) (X := X))=2^(Nat.card X-d) := by
  have hi := kernel_mul_embedding_index b hb x0 htwo
  have hdvd : (fullEmbedding b hb x0).range.index ∣ 2^Nat.card X :=
    ⟨Nat.card (Kernel (A := A) (X := X)),by simpa only [Nat.mul_comm] using hi.symm⟩
  obtain ⟨d,hd,he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  refine ⟨d,hd,he,?_⟩
  apply cancel_positive_right (pow_pos (by decide : 0<(2:ℕ)) d)
  rw [← he,hi,he,← pow_add,Nat.sub_add_cancel hd]

include hb in
theorem class_card_bounds (htwo : Nat.card (originalBlockFibre b x0)=2) :
    ∃ d≤Nat.card X,
      Nat.card (Kernel (A := A) (X := X))=2^(Nat.card X-d) ∧
      Nat.card (ConjClasses A)≤2^(Nat.card X-d) *
        Nat.card (ConjClasses (Top (A := A) (X := X))) ∧
      Nat.card (ConjClasses A)≤2^d *
        Nat.card (ConjClasses (FullWreath (A := A) b x0)) := by
  obtain ⟨d,hd,hi,hk⟩ := exists_codimension b hb x0 htwo
  refine ⟨d,hd,hk,?_,?_⟩
  · have hclass : Nat.card (ConjClasses (Kernel (A := A) (X := X)))≤
        Nat.card (Kernel (A := A) (X := X)) :=
      Nat.card_le_card_of_surjective ConjClasses.mk ConjClasses.mk_surjective
    have h := conjugacyClass_card_le_kernel_mul_range (topMap (A := A) (X := X))
    have hh := Nat.mul_le_mul_right
      (Nat.card (ConjClasses (Top (A := A) (X := X)))) hclass
    rw [hk] at hh
    exact h.trans hh
  · have h := ConjugacyClassSubgroupIndexBound.class_card_le_injective_index
      (fullEmbedding b hb x0) (fullEmbedding_injective b hb x0)
    simpa only [hi] using h

end SymmetricSubgroupAsymptotics.BinaryBlockWreathCodimension
