import SymmetricSubgroupAsymptotics.SubnormalCoordinateProperClassPowerSaving
import SymmetricSubgroupAsymptotics.ActualBlockProperClassDichotomy

/-! Proper-coordinate POWER saving for the same original block kernel,
or an actual equivalence with its saturated full wreath product. No
comparison with a larger base is made in the deficient-kernel branch. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.ActualBlockProperClassPowerDichotomy
open OriginalBlockClassBound ActualBlockCommonKernelCoordinates

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [MulAction.IsPretransitive A X] [FaithfulSMul A Ω]
    [Finite A] [Finite Ω] [Finite X]
    (b : Ω → X) (hb : ∀ (a : A) (ω : Ω), b (a • ω) = a • b ω) (x0 : X)

theorem kernel_power_saving_or_full_wreath (d B P : ℕ)
    (hbudget : ∀ L : Subgroup (originalBlockComponent b hb x0), L.IsSubnormal →
      Nat.card (ConjClasses L) ^ d ≤ B)
    (hproper : ∀ L : Subgroup (originalBlockComponent b hb x0), L.IsSubnormal → L ≠ ⊤ →
      Nat.card (ConjClasses L) ^ d ≤ P) :
    Nat.card (ConjClasses (Kernel (A := A) (X := X))) ^ d ≤ P * B ^ (Nat.card X - 1) ∨
      Nonempty (A ≃* PermutationalWreathProduct (originalBlockComponent b hb x0)
        (Top (A := A) (X := X)) X) := by
  letI : Fintype X := Fintype.ofFinite _
  by_cases hcard : Nat.card (Kernel (A := A) (X := X)) <
      Nat.card (originalBlockComponent b hb x0) ^ Nat.card X
  · left
    let e := (Fintype.equivFin X).symm
    have hi : Function.Injective
        (fun k => fun j : Fin (Fintype.card X) => kernelCoordinate b hb x0 (e j) k) := by
      intro k l he
      apply kernelCoordinates_injective b hb x0
      funext i
      obtain ⟨j, rfl⟩ := e.surjective i
      exact congrFun he j
    have hc : Nat.card (Kernel (A := A) (X := X)) <
        ∏ _j : Fin (Fintype.card X), Nat.card (originalBlockComponent b hb x0) := by
      simpa only [Fin.prod_const, Nat.card_eq_fintype_card] using hcard
    have h := SubnormalCoordinateProperClassPowerSaving.class_power_le_of_card_lt_product
      d (Fintype.card X) B P (fun _ => originalBlockComponent b hb x0)
      (fun _ => hbudget) (fun _ => hproper) (Kernel (A := A) (X := X))
      (fun j => kernelCoordinate b hb x0 (e j))
      (fun j => (kernelCoordinate_range_normal b hb x0 (e j)).isSubnormal) hi hc
    simpa only [Nat.card_eq_fintype_card] using h
  · have he : Nat.card (Kernel (A := A) (X := X)) =
        Nat.card (originalBlockComponent b hb x0) ^ Nat.card X :=
      (kernel_card_le_component_power b hb x0).antisymm (le_of_not_gt hcard)
    exact Or.inr ⟨ActualBlockFullWreathSaturation.fullWreathEquiv b hb x0 he⟩

theorem class_power_saving_or_full_wreath (d B P : ℕ)
    (hbudget : ∀ L : Subgroup (originalBlockComponent b hb x0), L.IsSubnormal →
      Nat.card (ConjClasses L) ^ d ≤ B)
    (hproper : ∀ L : Subgroup (originalBlockComponent b hb x0), L.IsSubnormal → L ≠ ⊤ →
      Nat.card (ConjClasses L) ^ d ≤ P) :
    Nat.card (ConjClasses A) ^ d ≤ (P * B ^ (Nat.card X - 1)) *
        Nat.card (ConjClasses (Top (A := A) (X := X))) ^ d ∨
      Nonempty (A ≃* PermutationalWreathProduct (originalBlockComponent b hb x0)
        (Top (A := A) (X := X)) X) := by
  rcases kernel_power_saving_or_full_wreath b hb x0 d B P hbudget hproper with h | h
  · have hs := Nat.pow_le_pow_left
      (conjugacyClass_card_le_kernel_mul_range (topMap (A := A) (X := X))) d
    rw [mul_pow] at hs
    exact Or.inl (hs.trans (Nat.mul_le_mul_right _ h))
  · exact Or.inr h

end SymmetricSubgroupAsymptotics.ActualBlockProperClassPowerDichotomy
