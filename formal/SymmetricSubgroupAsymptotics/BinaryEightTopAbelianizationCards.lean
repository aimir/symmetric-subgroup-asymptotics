import SymmetricSubgroupAsymptotics.BinaryEightOriginalRowActions
import SymmetricSubgroupAsymptotics.RDTDegreeEightE8Action

/-! Exact full abelianization orders of the two literal eight-point tops.
Regularity is checked on the original eight rows. The Heisenberg order
uses its proved literal action equivalence and actual derived subgroup. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryEightTopAbelianizationCards

open BinaryEightOriginalRowActions

private theorem regular_rows_square : ∀ i : Fin 8, ∀ x : Fin 8,
    (regularRow i : Equiv.Perm (Fin 8)) ((regularRow i : Equiv.Perm (Fin 8)) x) = x := by
  decide +kernel

theorem regular_pow_two (g : regularH) : g ^ 2 = 1 := by
  obtain ⟨i, rfl⟩ := regularRow_bijective.2 g
  apply Subtype.ext
  apply Equiv.ext
  exact regular_rows_square i

local instance regular_commutative : IsMulCommutative regularH :=
  ⟨⟨fun a b => (Commute.of_orderOf_dvd_two
    (fun g => orderOf_dvd_iff_pow_eq_one.mpr (regular_pow_two g)) a b).eq⟩⟩

theorem regular_abelianization_card : Nat.card (Abelianization regularH) = 8 := by
  have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup (commutator regularH)
  have hd : Nat.card (commutator regularH) = 1 := by
    rw [commutator_eq_bot, Subgroup.card_bot]
  rw [hd, mul_one] at hc
  exact hc.symm.trans BinaryMenuCayley8T3.exact_card

theorem heisenberg_abelianization_card : Nat.card (Abelianization heisenbergH) = 16 := by
  have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (commutator (BinaryHeisenberg 2))
  have hg : Nat.card (BinaryHeisenberg 2) = 32 := by
    norm_num only [BinaryHeisenberg.card]
  rw [hg, RDTDegreeEightE8Structure.commutator_card] at hc
  have he := Nat.card_congr RDTDegreeEightE8Action.modelEquiv.abelianizationCongr.toEquiv
  change Nat.card (Abelianization (BinaryHeisenberg 2)) =
    Nat.card (Abelianization heisenbergH) at he
  change 32 = Nat.card (Abelianization (BinaryHeisenberg 2)) * 2 at hc
  omega

end SymmetricSubgroupAsymptotics.BinaryEightTopAbelianizationCards
