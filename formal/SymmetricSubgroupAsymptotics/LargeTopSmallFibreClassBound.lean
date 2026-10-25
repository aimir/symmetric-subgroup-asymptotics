import SymmetricSubgroupAsymptotics.LargePrimitiveSmallFibreClassNumerics
import SymmetricSubgroupAsymptotics.PermutationBlockClassReduction
import SymmetricSubgroupAsymptotics.SmallPermutationClassBudgets
import SymmetricSubgroupAsymptotics.GaronziMarotiLargeBlockReduction

/-! Actual binary and ternary block actions with a large top of proved
quasipolynomial order satisfy the GM cube. The ternary kernel uses class
budgets for its literal S3 coordinates, not its larger order bound.
No primitive classification or independent-coordinate premise is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.LargeTopSmallFibreClassBound
open OriginalBlockClassBound SmallPermutationClassBudgets

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [Finite A] [Finite Ω] [Finite X] [FaithfulSMul A Ω]

private theorem class_card_le_power_mul_top (b : Ω → X)
    (hb : ∀ (a : A) (ω : Ω), b (a • ω) = a • b ω) (c : ℕ)
    (hc : ∀ x (L : Subgroup (Equiv.Perm (originalBlockFibre b x))),
      Nat.card (ConjClasses L) ≤ c) :
    Nat.card (ConjClasses A) ≤ c ^ Nat.card X *
      Nat.card (Top (A := A) (X := X)) := by
  letI : Fintype X := Fintype.ofFinite _
  have h := PermutationBlockClassReduction.class_card_le_product_mul_top b hb
    (fun _ => c) hc
  have ht : Nat.card (ConjClasses (Top (A := A) (X := X))) ≤
      Nat.card (Top (A := A) (X := X)) :=
    Nat.card_le_card_of_surjective (@ConjClasses.mk (Top (A := A) (X := X)) _)
      ConjClasses.mk_surjective
  have hp : Nat.card (ConjClasses A) ≤ c ^ Nat.card X *
      Nat.card (ConjClasses (Top (A := A) (X := X))) := by
    simpa only [Finset.prod_const,Finset.card_univ,Nat.card_eq_fintype_card] using h
  exact hp.trans (Nat.mul_le_mul_left _ ht)

theorem ternary_kernel_class_card_le_power (b : Ω → X)
    (hb : ∀ (a : A) (ω : Ω), b (a • ω) = a • b ω)
    (hsize : ∀ x, Nat.card (originalBlockFibre b x) ≤ 3) :
    Nat.card (ConjClasses (Kernel (A := A) (X := X))) ≤ 3 ^ Nat.card X := by
  letI : Fintype X := Fintype.ofFinite _
  have h := PermutationBlockClassReduction.kernel_class_card_le_product b hb
    (fun _ => 3) (fun x L => subgroup_class_card_le_three (hsize x) L)
  simpa only [Finset.prod_const,Finset.card_univ,Nat.card_eq_fintype_card] using h

theorem binary_class_cube_le (b : Ω → X)
    (hb : ∀ (a : A) (ω : Ω), b (a • ω) = a • b ω)
    (hsize : ∀ x, Nat.card (originalBlockFibre b x) = 2)
    (hn : 4096 ≤ Nat.card X)
    (horder : Nat.card (Top (A := A) (X := X)) ≤
      Nat.card X ^ (4 * Nat.log 2 (Nat.card X) + 24)) :
    Nat.card (ConjClasses A) ^ 3 ≤ 5 ^ (Nat.card Ω - 1) := by
  have hc := class_card_le_power_mul_top b hb 2
    (fun x L => subgroup_class_card_le_two (hsize x).le L)
  have hcube := (Nat.pow_le_pow_left hc 3).trans
    (LargePrimitiveSmallFibreClassNumerics.binary_product_cube_le
      (Nat.card X) (Nat.card (Top (A := A) (X := X))) hn horder)
  have he := GaronziMarotiLargeBlockReduction.card_eq_blocks_mul_fibre b 2 hsize
  simpa only [he,Nat.mul_comm (Nat.card X) 2] using hcube

theorem ternary_class_cube_le (b : Ω → X)
    (hb : ∀ (a : A) (ω : Ω), b (a • ω) = a • b ω)
    (hsize : ∀ x, Nat.card (originalBlockFibre b x) = 3)
    (hn : 4096 ≤ Nat.card X)
    (horder : Nat.card (Top (A := A) (X := X)) ≤
      Nat.card X ^ (4 * Nat.log 2 (Nat.card X) + 24)) :
    Nat.card (ConjClasses A) ^ 3 ≤ 5 ^ (Nat.card Ω - 1) := by
  have hc := class_card_le_power_mul_top b hb 3
    (fun x L => subgroup_class_card_le_three (hsize x).le L)
  have hcube := (Nat.pow_le_pow_left hc 3).trans
    (LargePrimitiveSmallFibreClassNumerics.ternary_product_cube_le
      (Nat.card X) (Nat.card (Top (A := A) (X := X))) hn horder)
  have he := GaronziMarotiLargeBlockReduction.card_eq_blocks_mul_fibre b 3 hsize
  simpa only [he,Nat.mul_comm (Nat.card X) 3] using hcube

end SymmetricSubgroupAsymptotics.LargeTopSmallFibreClassBound
