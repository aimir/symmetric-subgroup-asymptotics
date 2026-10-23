import SymmetricSubgroupAsymptotics.ThreePointPermutationClassBound
import Mathlib.Data.Fintype.EquivFin

/-! Structural class budgets for every subgroup of each literal small
fibre permutation group. Relabelling transports the SAME subgroup;
no subgroup class-count monotonicity is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SmallPermutationClassBudgets
open ThreePointPermutationClassBound

theorem subgroup_class_card_le_two {Y : Type*} [Finite Y]
    (hY:Nat.card Y≤2) (L:Subgroup (Equiv.Perm Y)) : Nat.card (ConjClasses L)≤2 := by
  have horder := L.card_le_card_group
  rw [Nat.card_perm] at horder
  have hfactorial : (Nat.card Y).factorial≤2 := by simpa using Nat.factorial_le hY
  exact (Nat.card_le_card_of_surjective (@ConjClasses.mk L _) ConjClasses.mk_surjective).trans
    (horder.trans hfactorial)

theorem subgroup_class_card_le_three {Y : Type*} [Finite Y]
    (hY:Nat.card Y≤3) (L:Subgroup (Equiv.Perm Y)) : Nat.card (ConjClasses L)≤3 := by
  by_cases htwo : Nat.card Y≤2
  · exact (subgroup_class_card_le_two htwo L).trans (by decide)
  · have hthree : Nat.card Y=3 := by omega
    let e : Y≃Fin 3 := Finite.equivFinOfCardEq hthree
    let T : Subgroup (Equiv.Perm (Fin 3)) := L.map e.permCongrHom.toMonoidHom
    let a : L≃*T := e.permCongrHom.subgroupMap L
    have h := Nat.card_le_card_of_surjective (ConjClasses.map a.symm.toMonoidHom)
      (ConjClasses.map_surjective a.symm.surjective)
    exact h.trans (ThreePointPermutationClassBound.subgroup_class_card_le_three T)

end SymmetricSubgroupAsymptotics.SmallPermutationClassBudgets
