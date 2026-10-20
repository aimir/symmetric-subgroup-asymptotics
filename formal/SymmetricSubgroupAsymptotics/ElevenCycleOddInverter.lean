import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.GroupTheory.Perm.Centralizer
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Tactic.Group
import Mathlib.Tactic.NormNum

/-! The only explicit witness has twelve points. Its five disjoint swaps
invert the displayed eleven-cycle and have odd sign. No group enumeration
or action-table certificate is used. -/
set_option autoImplicit false
open Equiv
namespace SymmetricSubgroupAsymptotics.ElevenCycleOddInverter

def cycle : Perm (Fin 12) := ([0,1,2,3,4,5,6,7,8,9,10] : List (Fin 12)).formPerm

def inverter : Perm (Fin 12) :=
  swap 1 10*swap 2 9*swap 3 8*swap 4 7*swap 5 6

theorem cycle_isCycle : cycle.IsCycle :=
  List.isCycle_formPerm (by decide) (by decide)

theorem cycle_support_card : cycle.support.card=11 := by decide +kernel

theorem cycle_order : orderOf cycle=11 :=
  cycle_isCycle.orderOf.trans cycle_support_card

theorem inverter_conjugates : inverter*cycle*inverter⁻¹=cycle⁻¹ := by decide +kernel

theorem inverter_sign : Perm.sign inverter = -1 := by
  simp [inverter,Perm.sign_swap (by decide : (1 : Fin 12)≠10),
    Perm.sign_swap (by decide : (2 : Fin 12)≠9),
    Perm.sign_swap (by decide : (3 : Fin 12)≠8),
    Perm.sign_swap (by decide : (4 : Fin 12)≠7),
    Perm.sign_swap (by decide : (5 : Fin 12)≠6)]

/-- Every order-eleven permutation of twelve points has an actual odd
inverter, obtained by transporting the twelve-point witness. -/
theorem exists_odd_inverter (g : Perm (Fin 12)) (hg : orderOf g=11) :
    ∃ a : Perm (Fin 12),a*g*a⁻¹=g⁻¹ ∧ Perm.sign a = -1 := by
  classical
  have hc : g.IsCycle := Perm.isCycle_of_prime_order'
    (by rw [hg]; decide) (by rw [hg]; decide)
  have hs : g.support.card=11 := hc.orderOf.symm.trans hg
  obtain ⟨a,ha⟩ := isConj_iff.mp (cycle_isCycle.isConj hc (cycle_support_card.trans hs.symm))
  refine ⟨a*inverter*a⁻¹,?_,?_⟩
  · rw [←ha]
    calc
      (a*inverter*a⁻¹)*(a*cycle*a⁻¹)*(a*inverter*a⁻¹)⁻¹ =
          a*(inverter*cycle*inverter⁻¹)*a⁻¹ := by group
      _ = a*cycle⁻¹*a⁻¹ := by rw [inverter_conjugates]
      _ = (a*cycle*a⁻¹)⁻¹ := by group
  · simp [inverter_sign,mul_comm]

/-- The centralizer price is eleven, even with the twelfth fixed point. -/
theorem centralizer_card (g : Perm (Fin 12)) (hg : orderOf g=11) :
    Nat.card (Subgroup.centralizer ({g} : Set (Perm (Fin 12))))=11 := by
  classical
  have hc : g.IsCycle := Perm.isCycle_of_prime_order'
    (by rw [hg]; decide) (by rw [hg]; decide)
  have hs : g.support.card=11 := hc.orderOf.symm.trans hg
  rw [Perm.nat_card_centralizer,hc.cycleType,hs]
  norm_num

end SymmetricSubgroupAsymptotics.ElevenCycleOddInverter
