import SymmetricSubgroupAsymptotics.BlockKernelClassBound
import SymmetricSubgroupAsymptotics.ConjugacyClassRealCoordinateBound

/-! Unrestricted class-count recurrence for an actual faithful block
action. Every local bound controls ALL subgroups of the corresponding
literal fibre permutation group. Kernel correlations are retained by
the existing faithful coordinate filtration. No p-group premise or
monotonicity of class number under inclusion is used. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics.PermutationBlockClassReduction
open OriginalBlockClassBound ConjugacyClassRealCoordinateBound
variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]

theorem kernel_class_card_le_product [Finite A] [Finite Ω] [Fintype X] [FaithfulSMul A Ω]
    (b : Ω→X) (hb : ∀(a : A) (ω : Ω),b (a•ω)=a•b ω) (c : X→ℕ)
    (hc : ∀x (L : Subgroup (Equiv.Perm (originalBlockFibre b x))),
      Nat.card (ConjClasses L)≤c x) :
    Nat.card (ConjClasses (Kernel (A:=A) (X:=X)))≤∏x,c x :=
  conjugacyClass_card_le_finite_coordinate_bounds
    (fun x=>Equiv.Perm (originalBlockFibre b x)) c hc
    (Kernel (A:=A) (X:=X)) (coordinate b hb) (coordinates_injective b hb)

theorem class_card_le_product_mul_top [Finite A] [Finite Ω] [Fintype X] [FaithfulSMul A Ω]
    (b : Ω→X) (hb : ∀(a : A) (ω : Ω),b (a•ω)=a•b ω) (c : X→ℕ)
    (hc : ∀x (L : Subgroup (Equiv.Perm (originalBlockFibre b x))),
      Nat.card (ConjClasses L)≤c x) :
    Nat.card (ConjClasses A)≤(∏x,c x)*Nat.card (ConjClasses (Top (A:=A) (X:=X))) :=
  (conjugacyClass_card_le_kernel_mul_range (topMap (A:=A) (X:=X))).trans
    (Nat.mul_le_mul_right _ (kernel_class_card_le_product b hb c hc))

theorem kernel_real_class_card_le_product [Finite A] [Finite Ω] [Fintype X] [FaithfulSMul A Ω]
    (b : Ω→X) (hb : ∀(a : A) (ω : Ω),b (a•ω)=a•b ω) (c : X→ℝ) (hc0 : ∀x,0≤c x)
    (hc : ∀x (L : Subgroup (Equiv.Perm (originalBlockFibre b x))),
      (Nat.card (ConjClasses L):ℝ)≤c x) :
    (Nat.card (ConjClasses (Kernel (A:=A) (X:=X))):ℝ)≤∏x,c x :=
  class_card_le_coordinate_product (fun x=>Equiv.Perm (originalBlockFibre b x))
    c hc0 hc (Kernel (A:=A) (X:=X)) (coordinate b hb) (coordinates_injective b hb)

theorem real_class_card_le_product_mul_top [Finite A] [Finite Ω] [Fintype X] [FaithfulSMul A Ω]
    (b : Ω→X) (hb : ∀(a : A) (ω : Ω),b (a•ω)=a•b ω) (c : X→ℝ) (hc0 : ∀x,0≤c x)
    (hc : ∀x (L : Subgroup (Equiv.Perm (originalBlockFibre b x))),
      (Nat.card (ConjClasses L):ℝ)≤c x) :
    (Nat.card (ConjClasses A):ℝ)≤
      (∏x,c x)*(Nat.card (ConjClasses (Top (A:=A) (X:=X))):ℝ) := by
  have hs : (Nat.card (ConjClasses A):ℝ)≤
      (Nat.card (ConjClasses (Kernel (A:=A) (X:=X))):ℝ)*
        (Nat.card (ConjClasses (Top (A:=A) (X:=X))):ℝ) := by
    exact_mod_cast conjugacyClass_card_le_kernel_mul_range (topMap (A:=A) (X:=X))
  exact hs.trans (mul_le_mul_of_nonneg_right
    (kernel_real_class_card_le_product b hb c hc0 hc) (Nat.cast_nonneg _))

end SymmetricSubgroupAsymptotics.PermutationBlockClassReduction
