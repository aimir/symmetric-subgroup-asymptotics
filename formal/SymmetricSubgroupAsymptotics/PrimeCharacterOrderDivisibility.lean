import SymmetricSubgroupAsymptotics.PrimeCharacterSubgroupCapacity
import Mathlib.GroupTheory.Index

/-! The actual prime character quotient has order dividing the original
group order. This retains divisibility when a mere order bound is weaker. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable (p : ℕ) [Fact p.Prime]

theorem primeCharacters_pow_finrank_dvd_card
    (G : Type*) [Group G] [Finite G] :
    p ^ Module.finrank (ZMod p) (PrimeCharacters p G) ∣ Nat.card G := by
  have h := Subgroup.card_dvd_of_surjective (primeAbelianizationGroupMap p G)
    (primeAbelianizationGroupMap_surjective p G)
  change Nat.card (PrimeAbelianization p G) ∣ Nat.card G at h
  rw [Module.natCard_eq_pow_finrank (K := ZMod p)
    (V := PrimeAbelianization p G)] at h
  simpa only [Nat.card_zmod, Subspace.dual_finrank_eq] using h

end SymmetricSubgroupAsymptotics
