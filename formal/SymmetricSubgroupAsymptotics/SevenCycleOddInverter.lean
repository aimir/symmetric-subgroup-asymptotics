import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.GroupTheory.Perm.Centralizer
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Tactic.Group
import Mathlib.Tactic.NormNum

/-! Seven-point odd inversion witness, transported to any order-seven
permutation. Three disjoint swaps; no group enumeration. -/
set_option autoImplicit false
open Equiv
namespace SymmetricSubgroupAsymptotics.SevenCycleOddInverter

def cycle : Perm (Fin 7) := ([0,1,2,3,4,5,6] : List (Fin 7)).formPerm

def inverter : Perm (Fin 7) :=
  swap 1 6*swap 2 5*swap 3 4

theorem cycle_isCycle : cycle.IsCycle :=
  List.isCycle_formPerm (by decide) (by decide)

theorem cycle_support_card : cycle.support.card=7 := by decide +kernel

theorem cycle_order : orderOf cycle=7 :=
  cycle_isCycle.orderOf.trans cycle_support_card

theorem inverter_conjugates : inverter*cycle*inverter⁻¹=cycle⁻¹ := by decide +kernel

theorem inverter_sign : Perm.sign inverter = -1 := by
  simp [inverter,Perm.sign_swap (by decide : (1 : Fin 7)≠6),
    Perm.sign_swap (by decide : (2 : Fin 7)≠5),
    Perm.sign_swap (by decide : (3 : Fin 7)≠4)]

/-- Every order-seven permutation of seven points has an actual odd
inverter, obtained by transporting the seven-point witness. -/
theorem exists_odd_inverter (g : Perm (Fin 7)) (hg : orderOf g=7) :
    ∃ a : Perm (Fin 7),a*g*a⁻¹=g⁻¹ ∧ Perm.sign a = -1 := by
  classical
  have hc : g.IsCycle := Perm.isCycle_of_prime_order'
    (by rw [hg]; decide) (by rw [hg]; decide)
  have hs : g.support.card=7 := hc.orderOf.symm.trans hg
  obtain ⟨a,ha⟩ := isConj_iff.mp (cycle_isCycle.isConj hc (cycle_support_card.trans hs.symm))
  refine ⟨a*inverter*a⁻¹,?_,?_⟩
  · rw [←ha]
    calc
      (a*inverter*a⁻¹)*(a*cycle*a⁻¹)*(a*inverter*a⁻¹)⁻¹ =
          a*(inverter*cycle*inverter⁻¹)*a⁻¹ := by group
      _ = a*cycle⁻¹*a⁻¹ := by rw [inverter_conjugates]
      _ = (a*cycle*a⁻¹)⁻¹ := by group
  · simp [inverter_sign,mul_comm]

/-- The centralizer price is seven. -/
theorem centralizer_card (g : Perm (Fin 7)) (hg : orderOf g=7) :
    Nat.card (Subgroup.centralizer ({g} : Set (Perm (Fin 7))))=7 := by
  classical
  have hc : g.IsCycle := Perm.isCycle_of_prime_order'
    (by rw [hg]; decide) (by rw [hg]; decide)
  have hs : g.support.card=7 := hc.orderOf.symm.trans hg
  rw [Perm.nat_card_centralizer,hc.cycleType,hs]
  norm_num

end SymmetricSubgroupAsymptotics.SevenCycleOddInverter
