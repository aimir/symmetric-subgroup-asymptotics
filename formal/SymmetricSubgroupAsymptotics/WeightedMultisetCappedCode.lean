import SymmetricSubgroupAsymptotics.WeightedMultisetPartitionCode
import Mathlib.Data.Finite.Sigma

/-! A finite family of expanded multisets gives a genuine finite
weighted-block code. The mass cap is retained in the index subtype;
no bound on unselected members of the original family is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators

namespace SymmetricSubgroupAsymptotics.WeightedMultisetCappedCode
open WeightedMultisetPartitionCode
variable {α ι : Type*}

def Code (F : ι → Multiset α) (N : ℕ) :=
  Σ i : {i : ι // (F i).card ≤ N}, Data (F i.val)

instance codeFinite [Fintype ι] (F : ι → Multiset α) (N : ℕ) : Finite (Code F N) := by
  unfold Code
  infer_instance

theorem card_le [Fintype ι] (F : ι → Multiset α) (N : ℕ) :
    Nat.card (Code F N) ≤ Nat.card ι * 2^(N-1) := by
  change Nat.card (Σ i : {i : ι // (F i).card ≤ N}, Data (F i.val)) ≤ _
  rw [Nat.card_sigma]
  calc
    _ ≤ ∑ _i : {i : ι // (F i).card ≤ N}, 2^(N-1) :=
      Finset.sum_le_sum (fun i _ => (data_card_le (F i.val)).trans
        (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ))
          (Nat.sub_le_sub_right i.property 1)))
    _ = Nat.card {i : ι // (F i).card ≤ N} * 2^(N-1) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Nat.card_eq_fintype_card, Nat.cast_id]
    _ ≤ _ := Nat.mul_le_mul_right _
      (Nat.card_le_card_of_injective (fun i : {i : ι // (F i).card ≤ N} => i.val)
        Subtype.val_injective)

end SymmetricSubgroupAsymptotics.WeightedMultisetCappedCode
