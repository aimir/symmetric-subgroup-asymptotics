import SymmetricSubgroupAsymptotics.PrimitiveFourPointComponentClassData
import SymmetricSubgroupAsymptotics.SymmetricFourComponentClassBudgets
import SymmetricSubgroupAsymptotics.SubnormalRealCoordinateClassBound
import SymmetricSubgroupAsymptotics.GaronziMarotiLargeBlockReduction
import SymmetricSubgroupAsymptotics.SmallPermutationClassBudgets

/-! Primitive four-point components with a literal two- or three-point
top. A deficient correlated kernel pays the class bound directly. The
only remaining alternative is an actual saturated wreath equivalence
with the same original component, itself equivalent to S4. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.SmallTopPrimitiveFourComponentClassBound
open OriginalBlockClassBound ActualBlockCommonKernelCoordinates

theorem four_cap_cube_le (n k : ℕ) (hn : n = 2 ∨ n = 3)
    (hk : k ≤ 4 ^ n * n) : k ^ 3 ≤ 5 ^ (4 * n - 1) := by
  apply (Nat.pow_le_pow_left hk 3).trans
  rcases hn with rfl | rfl <;> decide +kernel

theorem proper_five_cap_cube_le (n k : ℕ) (hn : n = 2 ∨ n = 3)
    (hk : k ≤ (4 * 5 ^ (n - 1)) * n) : k ^ 3 ≤ 5 ^ (4 * n - 1) := by
  apply (Nat.pow_le_pow_left hk 3).trans
  rcases hn with rfl | rfl <;> decide +kernel

theorem class_cube_or_symmetric_full_wreath
    {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [MulAction.IsPretransitive A X] [FaithfulSMul A Ω]
    [Finite A] [Finite Ω] [Finite X]
    (b : Ω → X) (hb : ∀ (a : A) (ω : Ω), b (a • ω) = a • b ω) (x0 : X)
    (hblocks : Nat.card X = 2 ∨ Nat.card X = 3)
    (hprimitive : MulAction.IsPreprimitive
      (originalBlockComponent b hb x0) (originalBlockFibre b x0))
    (hdegree : Nat.card (originalBlockFibre b x0) = 4) :
    Nat.card (ConjClasses A) ^ 3 ≤ 5 ^ (Nat.card Ω - 1) ∨
      (Nonempty (originalBlockComponent b hb x0 ≃* Equiv.Perm (Fin 4)) ∧
        Nonempty (A ≃* PermutationalWreathProduct (originalBlockComponent b hb x0)
          (Top (A := A) (X := X)) X)) := by
  letI : Fintype X := Fintype.ofFinite _
  have ht : Nat.card (ConjClasses (Top (A := A) (X := X))) ≤ Nat.card X := by
    rcases hblocks with h | h
    · rw [h]
      exact SmallPermutationClassBudgets.subgroup_class_card_le_two h.le _
    · rw [h]
      exact SmallPermutationClassBudgets.subgroup_class_card_le_three h.le _
  have hd : Nat.card Ω = 4 * Nat.card X := by
    have h := Nat.card_congr (ActualBlockWreathEmbedding.productEquiv b hb x0)
    rw [Nat.card_prod,hdegree] at h
    exact h.symm
  rcases PrimitiveFourPointComponentClassData.all_subgroup_cap_or_symmetric
    (originalBlockFibre b x0) (originalBlockComponent b hb x0) hprimitive hdegree with
    hfour | he
  · left
    have hker : Nat.card (ConjClasses (Kernel (A := A) (X := X))) ≤
        4 ^ Nat.card X := by
      have h := SubnormalRealCoordinateClassBound.class_card_le_finite_subnormal_coordinate_bounds
        (fun _ : X => originalBlockComponent b hb x0) (fun _ => 4)
        (Kernel (A := A) (X := X)) (kernelCoordinate b hb x0)
        (fun i => (kernelCoordinate_range_normal b hb x0 i).isSubnormal)
        (fun _ L _ => hfour L) (kernelCoordinates_injective b hb x0)
      simpa only [Finset.prod_const,Finset.card_univ,Nat.card_eq_fintype_card] using h
    have hA := (conjugacyClass_card_le_kernel_mul_range
      (topMap (A := A) (X := X))).trans (Nat.mul_le_mul hker ht)
    rw [hd]
    exact four_cap_cube_le _ _ hblocks hA
  · let e := Classical.choice he
    rcases SymmetricFourComponentClassBudgets.class_saving_or_full_wreath b hb x0 e with
      hsaving | hfull
    · left
      have hA := hsaving.trans (Nat.mul_le_mul_left _ ht)
      rw [hd]
      exact proper_five_cap_cube_le _ _ hblocks hA
    · exact Or.inr ⟨⟨e⟩,hfull⟩

end SymmetricSubgroupAsymptotics.SmallTopPrimitiveFourComponentClassBound
