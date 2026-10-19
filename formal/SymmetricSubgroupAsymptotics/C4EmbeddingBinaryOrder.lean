import SymmetricSubgroupAsymptotics.C4CoordinateSurjectiveQuotient
import Mathlib.GroupTheory.PGroup

/-! A genuine injection into r cyclic-four coordinates implies binary
order with exponent at most2r; no elementary-group conclusion is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.C4EmbeddingBinaryOrder
variable {H : Type} [Group H] [Finite H] {r : ℕ}

theorem card_power (j : H →* (Fin r → Multiplicative (ZMod 4)))
    (hj : Function.Injective j) : ∃ s : ℕ, s≤2*r ∧ Nat.card H=2^s := by
  have hc : Nat.card (Fin r → Multiplicative (ZMod 4))=2^(2*r) := by
    have hh : Nat.card (Fin r → Multiplicative (ZMod 4))=4^r := by
      rw [Nat.card_fun,Nat.card_congr Multiplicative.toAdd]
      simp
    rw [hh,show (4 : ℕ)=2^2 by decide,←pow_mul]
  have hp : IsPGroup 2 (Fin r → Multiplicative (ZMod 4)) := IsPGroup.of_card hc
  obtain ⟨s,hs⟩ := (hp.of_injective j hj).exists_card_eq
  have hle : 2^s≤2^(2*r) := by
    rw [←hs,←hc]
    exact Nat.card_le_card_of_injective j hj
  exact ⟨s,(Nat.pow_le_pow_iff_right (by decide : 1<2)).mp hle,hs⟩

end SymmetricSubgroupAsymptotics.C4EmbeddingBinaryOrder
