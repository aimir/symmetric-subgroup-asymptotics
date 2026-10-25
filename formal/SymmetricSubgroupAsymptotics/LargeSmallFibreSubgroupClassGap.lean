import SymmetricSubgroupAsymptotics.LargeSmallFibreSubnormalGapNumerics
import SymmetricSubgroupAsymptotics.PermutationBlockClassReduction
import SymmetricSubgroupAsymptotics.SmallPermutationClassBudgets
import SymmetricSubgroupAsymptotics.GaronziMarotiLargeBlockReduction

/-! A uniform gap for every actual subgroup of a binary/ternary block
group with a large top of proved order. The subgroup's own kernel and
top image are retained; only the latter's order is bounded by the SAME
original top. This is not class-number monotonicity. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.LargeSmallFibreSubgroupClassGap
open OriginalBlockClassBound

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [Finite A] [Finite Ω] [Finite X] [FaithfulSMul A Ω]

theorem subgroup_class_card_le_power_mul_top (b : Ω → X)
    (hb : ∀ (a : A) (ω : Ω), b (a • ω) = a • b ω) (c : ℕ)
    (hlocal : ∀ x (L : Subgroup (Equiv.Perm (originalBlockFibre b x))),
      Nat.card (ConjClasses L) ≤ c) (H : Subgroup A) :
    Nat.card (ConjClasses H) ≤ c ^ Nat.card X *
      Nat.card (Top (A := A) (X := X)) := by
  letI : Fintype X := Fintype.ofFinite _
  have hbH : ∀ (h : H) (ω : Ω), b (h • ω) = h • b ω := fun h ω => hb h.val ω
  have hrec := PermutationBlockClassReduction.class_card_le_product_mul_top
    b hbH (fun _ => c) hlocal
  have hrec' : Nat.card (ConjClasses H) ≤ c ^ Nat.card X *
      Nat.card (ConjClasses (Top (A := H) (X := X))) := by
    simpa only [Finset.prod_const,Finset.card_univ,Nat.card_eq_fintype_card] using hrec
  have hTop : Top (A := H) (X := X) ≤ Top (A := A) (X := X) := by
    rintro _ ⟨h,rfl⟩
    exact ⟨h.val,rfl⟩
  have hcard : Nat.card (Top (A := H) (X := X)) ≤
      Nat.card (Top (A := A) (X := X)) :=
    Nat.card_le_card_of_injective (Subgroup.inclusion hTop) (Subgroup.inclusion_injective hTop)
  have hclasses : Nat.card (ConjClasses (Top (A := H) (X := X))) ≤
      Nat.card (Top (A := A) (X := X)) :=
    (Nat.card_le_card_of_surjective (@ConjClasses.mk (Top (A := H) (X := X)) _)
      ConjClasses.mk_surjective).trans hcard
  exact hrec'.trans (Nat.mul_le_mul_left _ hclasses)

theorem subgroup_class_cube_gap_of_top_order (b : Ω → X)
    (hb : ∀ (a : A) (ω : Ω), b (a • ω) = a • b ω)
    (c : ℕ) (hc : c = 2 ∨ c = 3)
    (hsize : ∀ x, Nat.card (originalBlockFibre b x) = c)
    (hn : 4096 ≤ Nat.card X)
    (horder : Nat.card (Top (A := A) (X := X)) ≤
      Nat.card X ^ (4 * Nat.log 2 (Nat.card X) + 30)) (H : Subgroup A) :
    Nat.card (ConjClasses H) ^ 3 ≤ 5 ^ (Nat.card Ω - 2) := by
  have hlocal : ∀ x (L : Subgroup (Equiv.Perm (originalBlockFibre b x))),
      Nat.card (ConjClasses L) ≤ c := by
    rcases hc with rfl | rfl
    · exact fun x L => SmallPermutationClassBudgets.subgroup_class_card_le_two (hsize x).le L
    · exact fun x L => SmallPermutationClassBudgets.subgroup_class_card_le_three (hsize x).le L
  have h := subgroup_class_card_le_power_mul_top b hb c hlocal H
  have hnum : (c ^ Nat.card X * Nat.card (Top (A := A) (X := X))) ^ 3 ≤
      5 ^ (c * Nat.card X - 2) := by
    rcases hc with rfl | rfl
    · exact LargeSmallFibreSubnormalGapNumerics.binary_product_cube_gap _ _ hn horder
    · exact LargeSmallFibreSubnormalGapNumerics.ternary_product_cube_gap _ _ hn horder
  have hcube := (Nat.pow_le_pow_left h 3).trans hnum
  have he := GaronziMarotiLargeBlockReduction.card_eq_blocks_mul_fibre b c hsize
  simpa only [he,Nat.mul_comm (Nat.card X) c] using hcube

end SymmetricSubgroupAsymptotics.LargeSmallFibreSubgroupClassGap
