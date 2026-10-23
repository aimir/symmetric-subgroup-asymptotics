import SymmetricSubgroupAsymptotics.BinaryBlockWreathCodimension
import Mathlib.Tactic.Ring

/-! Multiply the two sound full-codimension bounds for the SAME original
binary block group. The codimension cancels from their product, while
the actual top and its actual full wreath remain unchanged. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryBlockClassGeometricMean
open OriginalBlockClassBound BinaryBlockWreathCodimension

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [MulAction.IsPretransitive A X] [FaithfulSMul A Ω]
    [Finite A] [Finite Ω] [Finite X]
    (b : Ω → X) (hb : ∀ (a : A) (ω : Ω),b (a • ω)=a • b ω) (x0 : X)

include hb in
theorem class_square_le_actual_top_wreath
    (htwo : Nat.card (originalBlockFibre b x0)=2) :
    Nat.card (ConjClasses A)^2≤2^Nat.card X *
      Nat.card (ConjClasses (Top (A := A) (X := X))) *
      Nat.card (ConjClasses (FullWreath (A := A) b x0)) := by
  obtain ⟨d,hd,_,hfirst,hsecond⟩ := class_card_bounds b hb x0 htwo
  calc
    Nat.card (ConjClasses A)^2≤
        (2^(Nat.card X-d)*Nat.card (ConjClasses (Top (A := A) (X := X)))) *
        (2^d*Nat.card (ConjClasses (FullWreath (A := A) b x0))) := by
      simpa only [pow_two] using Nat.mul_le_mul hfirst hsecond
    _=(2^(Nat.card X-d)*2^d)*Nat.card (ConjClasses (Top (A := A) (X := X))) *
        Nat.card (ConjClasses (FullWreath (A := A) b x0)) := by ring
    _=2^Nat.card X*Nat.card (ConjClasses (Top (A := A) (X := X))) *
        Nat.card (ConjClasses (FullWreath (A := A) b x0)) := by
      rw [← pow_add,Nat.sub_add_cancel hd]

end SymmetricSubgroupAsymptotics.BinaryBlockClassGeometricMean
