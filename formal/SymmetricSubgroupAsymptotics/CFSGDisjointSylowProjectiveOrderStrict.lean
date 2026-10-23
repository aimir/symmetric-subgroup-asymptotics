import SymmetricSubgroupAsymptotics.CFSGDisjointSylowProjectiveOrder

/-! The opposite-Sylow product has a strict order margin whenever
the Sylow is nontrivial: equality would force its index to be divisible
by the defining prime, contradicting the actual Sylow index. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGDisjointSylowProjectiveOrder
open CFSGCentralKernelPElements
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem quotient_center_card_strict_lower (P Q : Sylow p G)
    (hPQ : (P : Subgroup G) ⊓ (Q : Subgroup G) = ⊥) (hP : 1 < Nat.card P) :
    Nat.card P ^ 2 < Nat.card (G ⧸ Subgroup.center G) := by
  have hle := quotient_center_card_lower P Q hPQ
  apply lt_of_le_of_ne hle
  intro he
  let f := QuotientGroup.mk' (Subgroup.center G)
  let S := P.mapSurjective (f := f) (QuotientGroup.mk'_surjective _)
  have hker : f.ker ≤ Subgroup.center G := by
    intro z hz
    exact (QuotientGroup.eq_one_iff z).mp hz
  have hS : Nat.card S = Nat.card P := by
    change Nat.card ((P : Subgroup G).map f) = Nat.card P
    exact p_subgroup_card_map f P (quotient_center_sylow_injective P Q hPQ)
      hker (P : Subgroup G) P.isPGroup'
  have hindex : (S : Subgroup (G ⧸ Subgroup.center G)).index = Nat.card P := by
    have hc := (S : Subgroup (G ⧸ Subgroup.center G)).card_mul_index
    rw [hS, ← he, pow_two] at hc
    exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := P)) hc
  obtain ⟨k, hk⟩ := P.isPGroup'.exists_card_eq
  have hk0 : k ≠ 0 := by
    intro hh
    rw [hh, pow_zero] at hk
    omega
  have hpdiv : p ∣ Nat.card P := by
    rw [hk]
    exact dvd_pow_self p hk0
  exact S.not_dvd_index (by simpa only [hindex] using hpdiv)

end SymmetricSubgroupAsymptotics.CFSGDisjointSylowProjectiveOrder
