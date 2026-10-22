import SymmetricSubgroupAsymptotics.CFSGTwistedAPairedFixedRoots
import SymmetricSubgroupAsymptotics.CFSGTypeAPrimitiveUnitSquare
import Mathlib.Tactic.Linarith

/-! Literal quadratic-extension parameters for the adjacent A2 case.
They provide a nonzero trace-skew parameter and a fixed scalar outside
{0,1} whenever the ORIGINAL rank-two guard q != 2 holds. No chosen
identification of the fixed subfield with another field is required. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedA2FieldWitness
open CFSGTwistedANaturalMatrices

theorem exists_skew_and_fixed_scalar (q : CFSG.PrimePower) (hq : 3 ≤ q.order) :
    ∃ t a : q.Extension 2, t ≠ 0 ∧ t ^ q.order = -t ∧
      a ≠ 0 ∧ a ≠ 1 ∧ a ^ q.order = a := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (q.Extension 2)ˣ)
  have hge : (g : q.Extension 2) ^ q.order ≠ (g : q.Extension 2) := by
    intro he
    have hu : g ^ (q.order - 1) = 1 := by
      apply Units.ext
      change (g : q.Extension 2) ^ (q.order - 1) = 1
      rw [pow_sub₀ _ (Units.ne_zero g) (by omega), pow_one, he,
        mul_inv_cancel₀ (Units.ne_zero g)]
    have hd := orderOf_dvd_of_pow_eq_one hu
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, extension_two_card] at hd
    have hb := Nat.le_of_dvd (by omega : 0 < q.order - 1) hd
    have hsq : q.order ^ 2 = q.order * q.order := pow_two _
    have hsub : q.order ^ 2 - 1 + 1 = q.order ^ 2 :=
      Nat.sub_add_cancel (by nlinarith)
    have hqsub : q.order - 1 + 1 = q.order := Nat.sub_add_cancel (by omega)
    nlinarith
  have hnorm : (g : q.Extension 2) * (g : q.Extension 2) ^ q.order ≠ 1 := by
    intro he
    have hu : g ^ (q.order + 1) = 1 := by
      apply Units.ext
      change (g : q.Extension 2) ^ (q.order + 1) = 1
      simpa only [pow_succ, mul_comm] using he
    have hd := orderOf_dvd_of_pow_eq_one hu
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, extension_two_card] at hd
    have hb := Nat.le_of_dvd (by omega : 0 < q.order + 1) hd
    have hsq : q.order ^ 2 = q.order * q.order := pow_two _
    have hsub : q.order ^ 2 - 1 + 1 = q.order ^ 2 :=
      Nat.sub_add_cancel (by nlinarith)
    have hqsub : q.order - 1 + 1 = q.order := Nat.sub_add_cancel (by omega)
    nlinarith
  refine ⟨(g : q.Extension 2) - (g : q.Extension 2) ^ q.order,
    (g : q.Extension 2) * (g : q.Extension 2) ^ q.order, ?_, ?_, ?_, hnorm, ?_⟩
  · exact sub_ne_zero.mpr (Ne.symm hge)
  · have h := map_sub (CFSGSerreOrdinaryTwists.definingFieldAutomorphism q 2)
      (g : q.Extension 2) ((g : q.Extension 2) ^ q.order)
    change (((g : q.Extension 2) - (g : q.Extension 2) ^ q.order) ^ q.order) =
      (g : q.Extension 2) ^ q.order - ((g : q.Extension 2) ^ q.order) ^ q.order at h
    rw [h, extension_two_pow_twice]
    ring
  · exact mul_ne_zero (Units.ne_zero g) (pow_ne_zero _ (Units.ne_zero g))
  · rw [mul_pow, extension_two_pow_twice, mul_comm]

end SymmetricSubgroupAsymptotics.CFSGTwistedA2FieldWitness
