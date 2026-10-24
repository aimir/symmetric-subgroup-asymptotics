import SymmetricSubgroupAsymptotics.MarkedC4GeneratorNumbers

/-! Ordinary generator rank from the actual finite group order. These
bounds keep the binary exponent, rather than replacing it by twice itself. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FiniteGroupBinaryOrderGenerators

theorem two_pow_genRank_le_card (G : Type) [Group G] [Finite G] :
    2^MarkedC4.genRank G≤Nat.card G := by
  obtain ⟨S,hgen,hcard⟩ := MarkedC4.exists_generating_finset_card_le G
  exact (Nat.pow_le_pow_right (by decide : 0<2) (MarkedC4.genRank_le hgen)).trans hcard

theorem genRank_le_of_card_le_two_pow (G : Type) [Group G] [Finite G]
    (d : ℕ) (hcard : Nat.card G≤2^d) : MarkedC4.genRank G≤d :=
  (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp
    ((two_pow_genRank_le_card G).trans hcard)

theorem genRank_le_mul_of_card_le_pow (G : Type) [Group G] [Finite G]
    (p b d : ℕ) (hp : p≤2^b) (hcard : Nat.card G≤p^d) :
    MarkedC4.genRank G≤b*d := by
  apply genRank_le_of_card_le_two_pow G (b*d)
  calc
    Nat.card G≤p^d := hcard
    _≤(2^b)^d := Nat.pow_le_pow_left hp d
    _=2^(b*d) := (pow_mul 2 b d).symm

theorem genRank_le_pred_mul_of_card_le_pow (G : Type) [Group G] [Finite G]
    (p d : ℕ) (hp : 0<p) (hcard : Nat.card G≤p^d) :
    MarkedC4.genRank G≤(p-1)*d := by
  apply genRank_le_mul_of_card_le_pow G p (p-1) d ?_ hcard
  have h := (p-1).lt_two_pow_self
  omega

end SymmetricSubgroupAsymptotics.FiniteGroupBinaryOrderGenerators
