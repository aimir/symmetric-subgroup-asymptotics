import SymmetricSubgroupAsymptotics.CFSGTwistedA2FixedField
import SymmetricSubgroupAsymptotics.CFSGTwistedA2FieldWitness
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-! Exact trace fibres in the literal quadratic extension. A nonzero
trace-skew parameter identifies the trace kernel with the actual fixed
subfield; finite additive quotient counting proves trace surjectivity. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedA2TraceFibers
open CFSGSerreOrdinaryTwists CFSGTwistedANaturalMatrices
open CFSGTwistedA2FixedField CFSGTwistedA2FieldWitness

def traceHom (q : CFSG.PrimePower) : q.Extension 2 →+ q.Extension 2 :=
  AddMonoidHom.id (q.Extension 2) + (definingFieldAutomorphism q 2).toAddMonoidHom

@[simp] theorem traceHom_apply (q : CFSG.PrimePower) (x : q.Extension 2) :
    traceHom q x = x + definingFieldAutomorphism q 2 x := rfl

theorem trace_fixed (q : CFSG.PrimePower) (x : q.Extension 2) :
    traceHom q x ∈ fixedField q := by
  change definingFieldAutomorphism q 2 (x + definingFieldAutomorphism q 2 x) =
    x + definingFieldAutomorphism q 2 x
  rw [map_add]
  have h := extension_two_pow_twice q x
  change definingFieldAutomorphism q 2 (definingFieldAutomorphism q 2 x) = x at h
  rw [h, add_comm]

def traceKernelEquivFixed (q : CFSG.PrimePower) (t : q.Extension 2)
    (ht : t ≠ 0) (hts : t ^ q.order = -t) : (traceHom q).ker ≃ fixedField q where
  toFun x := ⟨x.val / t, by
    have hx : x.val + definingFieldAutomorphism q 2 x.val = 0 := x.property
    have hxs : definingFieldAutomorphism q 2 x.val = -x.val := by linear_combination hx
    change definingFieldAutomorphism q 2 (x.val / t) = x.val / t
    rw [map_div₀, hxs]
    change -x.val / (t ^ q.order) = x.val / t
    rw [hts, neg_div_neg_eq]⟩
  invFun a := ⟨t * a.val, by
    change t * a.val + definingFieldAutomorphism q 2 (t * a.val) = 0
    rw [map_mul]
    have ha : definingFieldAutomorphism q 2 a.val = a.val := a.property
    change t * a.val + t ^ q.order * definingFieldAutomorphism q 2 a.val = 0
    rw [hts, ha]
    ring⟩
  left_inv x := by
    apply Subtype.ext
    change t * (x.val / t) = x.val
    field_simp [ht]
  right_inv a := by
    apply Subtype.ext
    change (t * a.val) / t = a.val
    field_simp [ht]

theorem trace_kernel_card (q : CFSG.PrimePower) (hq : 3 ≤ q.order) :
    Nat.card (traceHom q).ker = q.order := by
  obtain ⟨t, a, ht, hts, _, _, _⟩ := exists_skew_and_fixed_scalar q hq
  exact (Nat.card_congr (traceKernelEquivFixed q t ht hts)).trans (fixedField_card q)

theorem trace_range_card (q : CFSG.PrimePower) (hq : 3 ≤ q.order) :
    Nat.card (traceHom q).range = q.order := by
  have hc := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (traceHom q).ker
  rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivRange (traceHom q)).toEquiv,
    trace_kernel_card q hq, extension_two_card, pow_two] at hc
  exact mul_right_cancel₀ (by omega : q.order ≠ 0) hc.symm

def rangeToFixed (q : CFSG.PrimePower) : (traceHom q).range → fixedField q :=
  fun x => ⟨x.val, by obtain ⟨y, hy⟩ := x.property; rw [← hy]; exact trace_fixed q y⟩

theorem rangeToFixed_injective (q : CFSG.PrimePower) : Function.Injective (rangeToFixed q) := by
  intro x y h
  apply Subtype.ext
  exact congrArg (fun z : fixedField q => z.val) h

theorem rangeToFixed_surjective (q : CFSG.PrimePower) (hq : 3 ≤ q.order) :
    Function.Surjective (rangeToFixed q) := by
  exact ((rangeToFixed_injective q).bijective_of_nat_card_le (by
    rw [trace_range_card q hq, fixedField_card])).surjective

theorem exists_trace_eq_norm (q : CFSG.PrimePower) (hq : 3 ≤ q.order)
    (a : q.Extension 2) : ∃ b : q.Extension 2,
      b + definingFieldAutomorphism q 2 b = a * definingFieldAutomorphism q 2 a := by
  let σ := definingFieldAutomorphism q 2
  have hn : a * σ a ∈ fixedField q := by
    change σ (a * σ a) = a * σ a
    rw [map_mul]
    have h := extension_two_pow_twice q a
    change σ (σ a) = a at h
    rw [h, mul_comm]
  obtain ⟨x, hx⟩ := rangeToFixed_surjective q hq ⟨a * σ a, hn⟩
  obtain ⟨b, hb⟩ := x.property
  refine ⟨b, ?_⟩
  exact hb.trans (congrArg (fun y : fixedField q => y.val) hx)

end SymmetricSubgroupAsymptotics.CFSGTwistedA2TraceFibers
