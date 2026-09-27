import SymmetricSubgroupAsymptotics.RepeatedMarkerAllocationWeights
import SymmetricSubgroupAsymptotics.TernarySubspaceEnvelope
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Complete positive-profile bound for repeated markers

The label type is the already selected finite set of distinct characters.
An ordering is used only to inject its positive multiplicity profiles into
compositions. It does not quotient allocations or cancel a physical q!.
The ternary estimate retains the exact singleton factor.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics.RepeatedMarkerProfileBound

open FiniteLabelAllocations RepeatedMarkerAllocationWeights
open TernaryFullWeightReindex TernarySubspaceEnvelope

variable {Q : Type*} [Fintype Q] (g : ℕ)

/-- A fixed ordering of the selected labels gives a composition. -/
def profileComposition (a : PositiveProfile (Q := Q) g) : Composition g where
  blocks := List.ofFn (fun i : Fin (Fintype.card Q) =>
    (a.val ((Fintype.equivFin Q).symm i)).val)
  blocks_pos := by
    intro j hj
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hj
    exact a.property.1 _
  blocks_sum := by
    rw [List.sum_ofFn]
    exact ((Fintype.equivFin Q).symm.sum_comp
      (fun q => (a.val q).val)).trans a.property.2

theorem profileComposition_injective :
    Function.Injective (profileComposition (Q := Q) g) := by
  intro a b h
  have hb := congrArg Composition.blocks h
  change List.ofFn (fun i : Fin (Fintype.card Q) =>
      (a.val ((Fintype.equivFin Q).symm i)).val) =
    List.ofFn (fun i : Fin (Fintype.card Q) =>
      (b.val ((Fintype.equivFin Q).symm i)).val) at hb
  have hf := List.ofFn_injective hb
  apply Subtype.ext
  funext q
  apply Fin.ext
  simpa only [Equiv.symm_apply_apply] using congrFun hf ((Fintype.equivFin Q) q)

/-- This remains valid for the empty label type and g=0. -/
theorem positiveProfile_card_le :
    Nat.card (PositiveProfile (Q := Q) g) ≤ 2^(g-1) := by
  have h := Nat.card_le_card_of_injective (profileComposition (Q := Q) g)
    (profileComposition_injective g)
  simpa only [Nat.card_eq_fintype_card,composition_card] using h

theorem profile_excess (a : PositiveProfile (Q := Q) g) :
    (∑ q, ((a.val q).val-1))=g-Fintype.card Q := by
  rw [Finset.sum_tsub_distrib Finset.univ
    (fun q _ => a.property.1 q),a.property.2]
  simp

theorem profile_term_le (a : PositiveProfile (Q := Q) g) :
    (∏ q, (ternaryFullFactor (a.val q).val : ℝ) /
      (((a.val q).val).factorial : ℝ)) ≤
    (3:ℝ)^((((g-Fintype.card Q : ℕ):ℝ)^2)/4+
      15*((g-Fintype.card Q : ℕ):ℝ)/4) := by
  have hp := full_factor_product_le (fun q => (a.val q).val)
    (fun q => a.property.1 q)
  rw [profile_excess g a] at hp
  apply le_trans _ hp
  apply Finset.prod_le_prod
  · intro q _
    positivity
  · intro q _
    apply div_le_self (Nat.cast_nonneg _)
    exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos (a.val q).val)

/-- The full rational H sum is bounded using every positive profile,
without a supplied count or physical-collapse hypothesis. -/
theorem markerProfileSum_le_ternary :
    (markerProfileSum (Q := Q) g : ℝ) ≤
      (2:ℝ)^g * (3:ℝ)^((((g-Fintype.card Q : ℕ):ℝ)^2)/4+
        15*((g-Fintype.card Q : ℕ):ℝ)/4) := by
  have hsum : (markerProfileSum (Q := Q) g : ℝ) =
      ∑ a : PositiveProfile (Q := Q) g,
        ∏ q, (ternaryFullFactor (a.val q).val : ℝ) /
          (((a.val q).val).factorial : ℝ) := by
    unfold markerProfileSum profileSum
    push_cast <;> rfl
  rw [hsum]
  calc
    _ ≤ ∑ _a : PositiveProfile (Q := Q) g,
        (3:ℝ)^((((g-Fintype.card Q : ℕ):ℝ)^2)/4+
          15*((g-Fintype.card Q : ℕ):ℝ)/4) :=
      Finset.sum_le_sum (fun a _ => profile_term_le g a)
    _ = (Nat.card (PositiveProfile (Q := Q) g):ℝ) *
        (3:ℝ)^((((g-Fintype.card Q : ℕ):ℝ)^2)/4+
          15*((g-Fintype.card Q : ℕ):ℝ)/4) := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
        Nat.card_eq_fintype_card]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast (positiveProfile_card_le (Q := Q) g).trans
        (Nat.pow_le_pow_right (by decide) (Nat.sub_le g 1))

/-- Exact integer comparison 3^5<2^8 supplies the required logarithmic constant. -/
theorem logb_two_three_lt : Real.logb 2 3 < (8:ℝ)/5 := by
  have h := Real.logb_lt_logb (by norm_num : (1:ℝ)<2)
    (by norm_num : (0:ℝ)<3^5) (by norm_num : (3:ℝ)^5<2^8)
  rw [Real.logb_pow,Real.logb_pow,Real.logb_self_eq_one (by norm_num)] at h
  norm_num at h
  linarith

/-- The manuscript H bound, with its original quadratic coefficient. -/
theorem markerProfileSum_le_binary :
    (markerProfileSum (Q := Q) g : ℝ) ≤
      (2:ℝ)^(Real.logb 2 3 * ((g-Fintype.card Q : ℕ):ℝ)^2/4+
        6*((g-Fintype.card Q : ℕ):ℝ)+(g:ℝ)) := by
  apply (markerProfileSum_le_ternary (Q := Q) g).trans
  have hp : (3:ℝ)^((((g-Fintype.card Q : ℕ):ℝ)^2)/4+
      15*((g-Fintype.card Q : ℕ):ℝ)/4) =
      (2:ℝ)^(Real.logb 2 3 * ((((g-Fintype.card Q : ℕ):ℝ)^2)/4+
        15*((g-Fintype.card Q : ℕ):ℝ)/4)) := by
    rw [Real.rpow_mul (by norm_num : (0:ℝ)≤2),
      Real.rpow_logb (by norm_num : (0:ℝ)<2) (by norm_num) (by norm_num)]
  rw [hp,← Real.rpow_natCast (2:ℝ) g,
    ← Real.rpow_add (by norm_num : (0:ℝ)<2)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have hk : 0≤((g-Fintype.card Q : ℕ):ℝ) := Nat.cast_nonneg _
  have hl := mul_le_mul_of_nonneg_right logb_two_three_lt.le hk
  nlinarith

end SymmetricSubgroupAsymptotics.RepeatedMarkerProfileBound
