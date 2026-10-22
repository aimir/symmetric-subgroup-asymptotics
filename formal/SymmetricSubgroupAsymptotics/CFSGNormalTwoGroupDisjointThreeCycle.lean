import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Perm.Cycle.Type

/-! A normal two-subgroup cannot move a normalizing three-cycle to a
disjoint support: the actual commutator would have order three inside
that two-subgroup. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGNormalTwoGroupDisjointThreeCycle
open Equiv Equiv.Perm

theorem impossible {X : Type*} [Fintype X] [DecidableEq X]
    (P : Subgroup (Perm X)) (hP : IsPGroup 2 P)
    (g c : Perm X) (hg : g ∈ P)
    (hcN : c ∈ Subgroup.normalizer (P : Set (Perm X)))
    (hc : IsThreeCycle c) (hdisj : Perm.Disjoint c (g * c * g⁻¹)) : False := by
  have hm : c * g⁻¹ * c⁻¹ ∈ P :=
    ((Subgroup.mem_normalizer_iff.mp hcN) g⁻¹).mp (P.inv_mem hg)
  have hcomm : g * c * g⁻¹ * c⁻¹ ∈ P := by
    simpa only [mul_assoc] using P.mul_mem hg hm
  let a : P := ⟨g * c * g⁻¹ * c⁻¹, hcomm⟩
  have ha : orderOf a = 3 := by
    rw [Subgroup.orderOf_mk]
    rw [hdisj.symm.inv_right.orderOf]
    change Nat.lcm (orderOf ((MulAut.conj g) c)) (orderOf c⁻¹) = 3
    rw [MulEquiv.orderOf_eq, orderOf_inv, hc.orderOf, Nat.lcm_self]
  obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp hP) a
  have hd : 3 ∣ 2 ^ n := by rw [← hn, ha]
  exact (by decide : (3 : ℕ) ≠ 2)
    (Nat.prime_eq_prime_of_dvd_pow Nat.prime_three Nat.prime_two hd)

end SymmetricSubgroupAsymptotics.CFSGNormalTwoGroupDisjointThreeCycle
