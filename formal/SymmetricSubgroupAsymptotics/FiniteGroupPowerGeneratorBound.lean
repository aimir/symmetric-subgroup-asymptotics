import SymmetricSubgroupAsymptotics.MarkedC4GeneratorNumbers

/-! A deliberately coarse generator budget for a finite group whose
actual order is at most a power of a fixed local constant. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.MarkedC4

private theorem self_le_two_pow (n : ℕ) : n ≤ 2^n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      have hp : 0<2^n := pow_pos (by decide) _
      rw [pow_succ]
      omega

theorem exists_generating_finset_card_le_of_card_le_pow
    (G : Type) [Group G] [Finite G] (d a : ℕ)
    (hcard : Nat.card G ≤ d^a) :
    ∃ S : Finset G, Subgroup.closure (S : Set G)=⊤ ∧ S.card ≤ d*a := by
  obtain ⟨S,hS,hsize⟩ := exists_generating_finset_card_le G
  refine ⟨S,hS,?_⟩
  have hp : d^a ≤ 2^(d*a) := by
    calc
      d^a ≤ (2^d)^a := Nat.pow_le_pow_left (self_le_two_pow d) a
      _ = 2^(d*a) := (pow_mul 2 d a).symm
  exact (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp
    (hsize.trans (hcard.trans hp))

theorem genRank_le_of_card_le_pow
    (G : Type) [Group G] [Finite G] (d a : ℕ)
    (hcard : Nat.card G ≤ d^a) : genRank G ≤ d*a := by
  obtain ⟨S,hS,hcardS⟩ := exists_generating_finset_card_le_of_card_le_pow G d a hcard
  exact (genRank_le hS).trans hcardS

end SymmetricSubgroupAsymptotics.MarkedC4
