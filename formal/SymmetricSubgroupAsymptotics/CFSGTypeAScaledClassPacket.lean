import SymmetricSubgroupAsymptotics.TypeAScaledOrderEnvelope
import SymmetricSubgroupAsymptotics.CFSGTypeARankTwoClassCube
import SymmetricSubgroupAsymptotics.CFSGTypeAOriginalOrderUpper
import SymmetricSubgroupAsymptotics.CFSGTypeAProperIndexOrderBudget

/-! Whole-order exponential rectangles and the sharper rank-two class
bound pay scaled packets on the SAME original A model. All bounds are
proved metadata for literal proper subgroups, not action-row premises. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTypeAScaledClassPacket
open PrimitiveSocleRawStructure CFSGReduction

theorem scaled_class_cube_le_proper_index
    (r : ℕ) (q : CFSG.PrimePower)
    (hwindow : 8 ≤ r ∨ (5 ≤ r ∧ 3 ≤ q.order) ∨ (4 ≤ r ∧ 4 ≤ q.order) ∨
      (r=3 ∧ 5 ≤ q.order) ∨ (r=2 ∧ 5 ≤ q.order))
    [IsSimpleGroup (CFSG.Models.A r q)] [Finite (CFSG.Models.A r q)]
    (H : Subgroup (CFSG.Models.A r q)) (hH : H ≠ ⊤) :
    25*(Nat.card (ConjClasses (CFSG.Models.A r q))*
      Nat.card (Outer (CFSG.Models.A r q)))^3 ≤ 3^H.index := by
  have hr : 2 ≤ r := by rcases hwindow with h | h | h | h | h <;> omega
  have hq : 2 ≤ q.order := q.prime_isPrime.two_le.trans
    (Nat.le_self_pow q.exponent_pos.ne' q.prime)
  have hf : q.exponent ≤ q.order := q.exponent.lt_two_pow_self.le.trans
    (Nat.pow_le_pow_left q.prime_isPrime.two_le q.exponent)
  by_cases hr2 : r=2
  · subst r
    have hq5 : 5 ≤ q.order := by
      rcases hwindow with h | h | h | h | h <;> omega
    have hc := CFSGTypeARankTwoClassCube.class_card_le q
    have ho := CFSGTypeAOuterGcdCardinality.typeA_higher_outer_card_le_gcd 2 (by decide) q
    have hg : (q.order-1).gcd 3 ≤ 3 := Nat.gcd_le_right _ (by decide)
    have hcomponent : Nat.card (ConjClasses (CFSG.Models.A 2 q))*
        Nat.card (Outer (CFSG.Models.A 2 q)) ≤ 18*q.order*(q.order^2+2*q.order) := by
      exact (Nat.mul_le_mul hc ho).trans
        ((Nat.mul_le_mul (Nat.mul_le_mul_right _ hg)
          (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hg) hf)).trans_eq (by ring))
    exact ((Nat.mul_le_mul_left 25 (Nat.pow_le_pow_left hcomponent 3)).trans
      (TypeAScaledOrderEnvelope.rank_two_scaled_class_cube_le q.order hq5)).trans
        (Nat.pow_le_pow_right (by decide)
          (CFSGTypeARankTwoClassCube.proper_index_lower q H hH))
  · have hw : 8 ≤ r ∨ (5 ≤ r ∧ 3 ≤ q.order) ∨ (4 ≤ r ∧ 4 ≤ q.order) ∨
        (r=3 ∧ 5 ≤ q.order) := by
      rcases hwindow with h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
      · exact (hr2 h.1).elim
    have hrpow : 2*(r+1) ≤ q.order^(r+1) := by
      have hh : r+1 ≤ 2^r := Nat.succ_le_of_lt r.lt_two_pow_self
      have he : 2*(r+1) ≤ 2^(r+1) :=
        (Nat.mul_le_mul_left 2 hh).trans_eq (by rw [pow_succ]; ring)
      exact he.trans (Nat.pow_le_pow_left hq _)
    have ho : Nat.card (Outer (CFSG.Models.A r q)) ≤ q.order^(r+2) := by
      have hg : (q.order-1).gcd (r+1) ≤ r+1 := Nat.gcd_le_right _ (by omega)
      calc
        _ ≤ 2*((q.order-1).gcd (r+1))*q.exponent :=
          CFSGTypeAOuterGcdCardinality.typeA_higher_outer_card_le_gcd r hr q
        _ ≤ 2*(r+1)*q.exponent :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hg)
        _ ≤ q.order^(r+1)*q.order := Nat.mul_le_mul hrpow hf
        _ = q.order^(r+2) := (pow_succ q.order (r+1)).symm
    have hc : Nat.card (ConjClasses (CFSG.Models.A r q)) ≤ q.order^((r+1)^2) :=
      (Nat.card_le_card_of_surjective ConjClasses.mk ConjClasses.mk_surjective).trans
        (typeA_order_le_matrix_power r q)
    have hcomponent : Nat.card (ConjClasses (CFSG.Models.A r q))*
        Nat.card (Outer (CFSG.Models.A r q)) ≤ q.order^((r+2)^2) := by
      exact (Nat.mul_le_mul hc ho).trans
        (by
          rw [←pow_add]
          exact Nat.pow_le_pow_right (by omega) (by nlinarith))
    exact ((Nat.mul_le_mul_left 25 (Nat.pow_le_pow_left hcomponent 3)).trans
      (TypeAScaledOrderEnvelope.higher_scaled_order_cube_le q.order r hq hw)).trans
        (Nat.pow_le_pow_right (by decide)
          (CFSGTypeAProperIndexOrderBudget.typeA_higher_field_power_le_proper_index r hr q H hH))

end SymmetricSubgroupAsymptotics.CFSGTypeAScaledClassPacket
