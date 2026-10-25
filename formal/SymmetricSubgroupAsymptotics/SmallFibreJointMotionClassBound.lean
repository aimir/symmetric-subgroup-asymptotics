import SymmetricSubgroupAsymptotics.AbelianExtensionJointMotionClassBound
import SymmetricSubgroupAsymptotics.BinaryBlockKernelAbelian
import SymmetricSubgroupAsymptotics.TernaryBlockKernelCoordinates

/-! Joint class capacities of the ACTUAL binary block kernel and the
ACTUAL all-even ternary compression kernel. Correlations and local signs
are retained. These counts do not assert a final GM exponent bound. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SmallFibreJointMotionClassBound
open AbelianExtensionJointMotionClassBound OriginalBlockClassBound

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [Finite A] [Finite Ω] [FaithfulSMul A Ω]

def binaryCapacity (b : Ω → X)
    (hb : ∀ (a : A) (ω : Ω), b (a • ω) = a • b ω)
    (hsmall : ∀ x, Nat.card (originalBlockFibre b x) ≤ 2) : ℕ := by
  letI : IsMulCommutative (Kernel (A := A) (X := X)) :=
    BinaryBlockKernelAbelian.kernel_isMulCommutative b hb hsmall
  exact extensionJointCapacity (Kernel (A := A) (X := X))

theorem binary_class_card_mul_top_le (b : Ω → X)
    (hb : ∀ (a : A) (ω : Ω), b (a • ω) = a • b ω)
    (hsmall : ∀ x, Nat.card (originalBlockFibre b x) ≤ 2) :
    Nat.card (Top (A := A) (X := X)) * Nat.card (ConjClasses A) ≤
      binaryCapacity b hb hsmall := by
  letI : IsMulCommutative (Kernel (A := A) (X := X)) :=
    BinaryBlockKernelAbelian.kernel_isMulCommutative b hb hsmall
  have hc := class_card_mul_quotient_le (Kernel (A := A) (X := X))
  have he : Nat.card (A ⧸ Kernel (A := A) (X := X)) =
      Nat.card (Top (A := A) (X := X)) :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange
      (topMap (A := A) (X := X))).toEquiv
  rw [he] at hc
  exact hc

variable [MulAction.IsPretransitive A X]

def ternaryEvenCapacity (b : Ω → X)
    (hb : ∀ (a : A) (ω : Ω), b (a • ω) = a • b ω)
    (x₀ : X) (e : Fin 3 ≃ originalBlockFibre b x₀) : ℕ := by
  letI : IsMulCommutative (TernaryBlockKernelCoordinates.evenKernel b hb x₀ e) :=
    TernaryBlockKernelCoordinates.evenKernel_isMulCommutative b hb x₀ e
  exact extensionJointCapacity (TernaryBlockKernelCoordinates.evenKernel b hb x₀ e)

theorem ternary_class_card_mul_quotient_le (b : Ω → X)
    (hb : ∀ (a : A) (ω : Ω), b (a • ω) = a • b ω)
    (x₀ : X) (e : Fin 3 ≃ originalBlockFibre b x₀) :
    Nat.card (A ⧸ TernaryBlockKernelCoordinates.evenKernel b hb x₀ e) *
        Nat.card (ConjClasses A) ≤ ternaryEvenCapacity b hb x₀ e := by
  letI : IsMulCommutative (TernaryBlockKernelCoordinates.evenKernel b hb x₀ e) :=
    TernaryBlockKernelCoordinates.evenKernel_isMulCommutative b hb x₀ e
  exact class_card_mul_quotient_le (TernaryBlockKernelCoordinates.evenKernel b hb x₀ e)

end SymmetricSubgroupAsymptotics.SmallFibreJointMotionClassBound
