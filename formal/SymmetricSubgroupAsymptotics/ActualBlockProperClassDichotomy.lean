import SymmetricSubgroupAsymptotics.SubnormalCoordinateProperClassSaving
import SymmetricSubgroupAsymptotics.ActualBlockCommonKernelCoordinates
import SymmetricSubgroupAsymptotics.ActualBlockFullWreathSaturation

/-! The original block group has either a strict coordinate class
saving, or an actual equivalence to the full wreath product with its
SAME component and top. Proper correlated kernels are never compared
monotonically to a full base. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.ActualBlockProperClassDichotomy
open OriginalBlockClassBound ActualBlockCommonKernelCoordinates

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [MulAction.IsPretransitive A X] [FaithfulSMul A Ω]
    [Finite A] [Finite Ω] [Finite X]
    (b : Ω → X) (hb : ∀ (a : A) (ω : Ω), b (a • ω) = a • b ω) (x0 : X)

theorem kernel_saving_or_full_wreath (c : ℕ)
    (hbudget : ∀ L : Subgroup (originalBlockComponent b hb x0), L.IsSubnormal →
      Nat.card (ConjClasses L) ≤ c)
    (hproper : ∀ L : Subgroup (originalBlockComponent b hb x0), L.IsSubnormal → L ≠ ⊤ →
      Nat.card (ConjClasses L) ≤ c - 1) :
    Nat.card (ConjClasses (Kernel (A := A) (X := X))) ≤ (c - 1) * c ^ (Nat.card X - 1) ∨
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
      obtain ⟨j,rfl⟩ := e.surjective i
      exact congrFun he j
    have hc : Nat.card (Kernel (A := A) (X := X)) <
        ∏ _j : Fin (Fintype.card X), Nat.card (originalBlockComponent b hb x0) := by
      simpa only [Fin.prod_const,Nat.card_eq_fintype_card] using hcard
    have h := SubnormalCoordinateProperClassSaving.class_card_le_of_card_lt_product
      (Fintype.card X) c (fun _ => originalBlockComponent b hb x0)
      (fun _ => hbudget) (fun _ => hproper) (Kernel (A := A) (X := X))
      (fun j => kernelCoordinate b hb x0 (e j))
      (fun j => (kernelCoordinate_range_normal b hb x0 (e j)).isSubnormal) hi hc
    simpa only [Nat.card_eq_fintype_card] using h
  · have he : Nat.card (Kernel (A := A) (X := X)) =
        Nat.card (originalBlockComponent b hb x0) ^ Nat.card X :=
      (kernel_card_le_component_power b hb x0).antisymm (le_of_not_gt hcard)
    exact Or.inr ⟨ActualBlockFullWreathSaturation.fullWreathEquiv b hb x0 he⟩

theorem class_saving_or_full_wreath (c : ℕ)
    (hbudget : ∀ L : Subgroup (originalBlockComponent b hb x0), L.IsSubnormal →
      Nat.card (ConjClasses L) ≤ c)
    (hproper : ∀ L : Subgroup (originalBlockComponent b hb x0), L.IsSubnormal → L ≠ ⊤ →
      Nat.card (ConjClasses L) ≤ c - 1) :
    Nat.card (ConjClasses A) ≤
      ((c - 1) * c ^ (Nat.card X - 1)) * Nat.card (ConjClasses (Top (A := A) (X := X))) ∨
      Nonempty (A ≃* PermutationalWreathProduct (originalBlockComponent b hb x0)
        (Top (A := A) (X := X)) X) := by
  rcases kernel_saving_or_full_wreath b hb x0 c hbudget hproper with h | h
  · exact Or.inl ((conjugacyClass_card_le_kernel_mul_range (topMap (A := A) (X := X))).trans
      (Nat.mul_le_mul_right _ h))
  · exact Or.inr h

end SymmetricSubgroupAsymptotics.ActualBlockProperClassDichotomy
