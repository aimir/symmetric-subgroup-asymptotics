import SymmetricSubgroupAsymptotics.CFSGTwistedA2FixedField
import SymmetricSubgroupAsymptotics.CFSGTwistedA2UnipotentArrays
import Mathlib.Tactic.Linarith

/-! The literal quadratic-extension norm is onto its ACTUAL Frobenius
fixed field. In particular every second-coordinate parameter occurs in
an original norm-constrained upper array. No unitary model is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedA2UnipotentArrays
open CFSGSerreOrdinaryTwists CFSGTwistedA2FixedField
open CFSGTwistedANaturalMatrices

theorem normExponent (q : CFSG.PrimePower) :
    (q.order ^ 2 - 1) / (q.order - 1) = q.order + 1 := by
  have hq : 2 ≤ q.order := q.prime_isPrime.two_le.trans
    (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)
  have hs : q.order - 1 + 1 = q.order := Nat.sub_add_cancel (by omega)
  have ht : q.order ^ 2 - 1 + 1 = q.order ^ 2 := Nat.sub_add_cancel (by nlinarith)
  have hm : (q.order + 1) * (q.order - 1) = q.order ^ 2 - 1 := by nlinarith
  rw [← hm, Nat.mul_div_cancel _ (by omega : 0 < q.order - 1)]

theorem exists_norm_eq_fixed (q : CFSG.PrimePower) (c : q.Extension 2)
    (hc : definingFieldAutomorphism q 2 c = c) :
    ∃ a : q.Extension 2, a * definingFieldAutomorphism q 2 a = c := by
  let cF : fixedField q := ⟨c, hc⟩
  obtain ⟨a, ha⟩ := FiniteField.norm_surjective (fixedField q) (q.Extension 2) cF
  have hp := FiniteField.algebraMap_norm_eq_pow
    (K := fixedField q) (K' := q.Extension 2) (x := a)
  rw [ha] at hp
  change c = a ^ ((Nat.card (q.Extension 2) - 1) / (Nat.card (fixedField q) - 1)) at hp
  rw [extension_two_card, fixedField_card, normExponent] at hp
  refine ⟨a, ?_⟩
  change a * a ^ q.order = c
  simpa only [pow_succ, mul_comm] using hp.symm

theorem exists_first_parameter (q : CFSG.PrimePower) (b : q.Extension 2) :
    ∃ a : q.Extension 2, NormCondition (definingFieldAutomorphism q 2) a b := by
  let σ := definingFieldAutomorphism q 2
  have hs : σ (σ b) = b := extension_two_pow_twice q b
  have hb : σ (b + σ b) = b + σ b := by rw [map_add, hs, add_comm]
  obtain ⟨a, ha⟩ := exists_norm_eq_fixed q (b + σ b) hb
  exact ⟨a, ha.symm⟩

end SymmetricSubgroupAsymptotics.CFSGTwistedA2UnipotentArrays
