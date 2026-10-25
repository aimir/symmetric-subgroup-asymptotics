import SymmetricSubgroupAsymptotics.ElementarySylowPointStabilizerOrder

/-! The actual elementary Sylow subgroup in a faithful transitive binary
prime-power action has the full binary part of the original source order.
Consequently the next binary power cannot divide that SAME source order.
No group recognition or supplied order certificate is used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.ElementarySylowTransitiveOrderObstruction

variable {G X : Type} [Group G] [Finite G] [Finite X] [Nonempty X]
    [MulAction G X] [FaithfulSMul G X] [MulAction.IsPretransitive G X]

theorem next_power_not_dvd_card (P : Sylow 2 G)
    (hel : ∀ g : P, g^2 = 1) (k : ℕ) (hcard : Nat.card X = 2^k) :
    ¬2^(k+1) ∣ Nat.card G := by
  let x : X := Classical.choice inferInstance
  have hodd := ElementarySylowPointStabilizerOrder.two_not_dvd_stabilizer_card
    P hel k hcard x
  have hmul := (MulAction.stabilizer G x).card_mul_index
  rw [MulAction.index_stabilizer_of_transitive G x,hcard] at hmul
  intro hdiv
  have hcancel : 2^k*2 ∣ Nat.card G := by
    simpa only [pow_succ] using hdiv
  have hG : Nat.card G = 2^k*Nat.card (MulAction.stabilizer G x) := by
    simpa only [Nat.mul_comm] using hmul.symm
  rw [hG] at hcancel
  exact hodd ((Nat.mul_dvd_mul_iff_left (pow_pos (by decide : 0 < 2) k)).mp hcancel)

theorem sixteen_not_dvd_card_of_degree_eight (P : Sylow 2 G)
    (hel : ∀ g : P, g^2 = 1) (hcard : Nat.card X = 8) :
    ¬16 ∣ Nat.card G := by
  exact next_power_not_dvd_card P hel 3 hcard

end SymmetricSubgroupAsymptotics.ElementarySylowTransitiveOrderObstruction
