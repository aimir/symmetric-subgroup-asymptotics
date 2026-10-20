import SymmetricSubgroupAsymptotics.ScalarFourCentralC4CubicAllQuotients
import SymmetricSubgroupAsymptotics.C4EmbeddingBinaryOrder

set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ScalarFourCentralC4TopCoordinates
variable {Q : Type} [Group Q] [Finite Q] {c d : ℕ}
  (D : ScalarFourCentralC4TopCoordinates Q CyclicThree c d)

theorem cubic_all_original_binary_menu (hcubic : D.cubic=Multiplicative.ofAdd (1 : ZMod 3))
    (N : Subgroup Q) [N.Normal] :
    (∃ c' d' : ℕ, c'≤c ∧ d'≤d ∧
      Nonempty (ScalarFourCentralC4TopCoordinates (Q ⧸ N) CyclicThree c' d')) ∨
    (IsPGroup 2 (Q ⧸ N) ∧ Nat.card (Q ⧸ N)≤2^(2*c)) := by
  rcases D.all_original_quotients hcubic N with hret | hbin
  · exact Or.inl hret
  · obtain ⟨r,hr,j,hj⟩ := hbin
    obtain ⟨s,hs,hcard⟩ := C4EmbeddingBinaryOrder.card_power j hj
    refine Or.inr ⟨IsPGroup.of_card hcard,?_⟩
    rw [hcard]
    exact Nat.pow_le_pow_right (by decide) (by omega)

end SymmetricSubgroupAsymptotics.ScalarFourCentralC4TopCoordinates
