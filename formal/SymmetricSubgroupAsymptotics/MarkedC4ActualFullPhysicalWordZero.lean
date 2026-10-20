import SymmetricSubgroupAsymptotics.MarkedC4ActualFullPhysicalWordPeel
import SymmetricSubgroupAsymptotics.MarkedC4VerticalHallBase

/-! Correct zero-degree base for the actual recursive physical family.
The enlarged family retains vertical markers, so P(r) is divided ONCE. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualFullPhysicalWordZero
open ActualFullPhysicalWordPeel

theorem zero_card_le_subgroups (F : Fin 0 → Type) [∀ i,Group (F i)]
    (M : Type) [Group M] [Finite M] : Nat.card (Family F M)≤Nat.card (Subgroup M) := by
  have hpi : Function.Injective (MonoidHom.snd (∀ i,F i) M) := by
    intro x y he
    apply Prod.ext
    · funext i
      exact Fin.elim0 i
    · exact he
  let code : Family F M → Subgroup M := fun J => J.val.map (MonoidHom.snd (∀ i,F i) M)
  have hcode : Function.Injective code := by
    intro J K he
    apply Subtype.ext
    exact Subgroup.map_injective (f := MonoidHom.snd (∀ i,F i) M) hpi he
  exact Nat.card_le_card_of_injective code hcode

theorem zero_marked_le (F : Fin 0 → Type) [∀ i,Group (F i)] (r : ℕ) :
    (Nat.card (Family F (Multiplicative (Fin r → ZMod 4))) : ℝ)≤
      VerticalHallBase.polynomial r*(2 : ℝ)^markedF 0 r :=
  (Nat.cast_le.mpr (zero_card_le_subgroups F (Multiplicative (Fin r → ZMod 4)))).trans
    (VerticalHallBase.card_subgroups_le r)

/-- This is the zero condition for a recurrence normalized by P(r).
It does not assert the false unmarked bound for vertical mark subgroups. -/
theorem normalized_zero_le (F : Fin 0 → Type) [∀ i,Group (F i)] (r : ℕ) :
    (Nat.card (Family F (Multiplicative (Fin r → ZMod 4))) : ℝ)/VerticalHallBase.polynomial r≤
      (2 : ℝ)^markedF 0 r := by
  have hp : 0<VerticalHallBase.polynomial r := lt_of_lt_of_le (by norm_num : (0 : ℝ)<1)
    (VerticalHallBase.polynomial_one_le r)
  apply (div_le_iff₀ hp).mpr
  simpa only [mul_comm] using zero_marked_le F r

end SymmetricSubgroupAsymptotics.MarkedC4.ActualFullPhysicalWordZero
