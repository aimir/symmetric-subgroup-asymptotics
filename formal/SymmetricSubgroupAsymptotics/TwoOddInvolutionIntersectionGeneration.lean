import SymmetricSubgroupAsymptotics.OddInvolutionConjugateRecovery

/-! Two literal odd-period reflection recoveries upgrade the SAME
subgroup-head generation to generation by its two actual subgroups.
The ambient group and all subgroup inclusions are abstract here. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.TwoOddInvolutionIntersectionGeneration
variable {G : Type*} [Group G]

theorem sup_eq (P N D : Subgroup G) (t0 t1 s0 s1 : G) (k0 k1 : ℕ)
    (hPD : P ≤ D) (hND : N ≤ D)
    (hhead : D ≤ P ⊔ Subgroup.closure ({t0, t1} : Set G))
    (ht0 : t0 ^ 2 = 1) (ht1 : t1 ^ 2 = 1)
    (hs0 : s0 ^ 2 = 1) (hs1 : s1 ^ 2 = 1)
    (ho0 : (t0 * s0) ^ (2 * k0 + 1) = 1)
    (ho1 : (t1 * s1) ^ (2 * k1 + 1) = 1)
    (hp0 : s0 ∈ P) (hp1 : s1 ∈ P)
    (hn0 : t0 * s0 * t0 ∈ N) (hn1 : t1 * s1 * t1 ∈ N) : P ⊔ N = D := by
  have h0 : t0 ∈ P ⊔ N := OddInvolutionConjugateRecovery.mem_of_conjugate
    (P ⊔ N) t0 s0 k0 ht0 hs0 ho0
    (Subgroup.mem_sup_left hp0) (Subgroup.mem_sup_right hn0)
  have h1 : t1 ∈ P ⊔ N := OddInvolutionConjugateRecovery.mem_of_conjugate
    (P ⊔ N) t1 s1 k1 ht1 hs1 ho1
    (Subgroup.mem_sup_left hp1) (Subgroup.mem_sup_right hn1)
  have hc : Subgroup.closure ({t0, t1} : Set G) ≤ P ⊔ N := by
    apply (Subgroup.closure_le _).mpr
    intro z hz
    rcases hz with rfl | rfl
    · exact h0
    · exact h1
  exact le_antisymm (sup_le hPD hND) (hhead.trans (sup_le le_sup_left hc))

end SymmetricSubgroupAsymptotics.TwoOddInvolutionIntersectionGeneration
