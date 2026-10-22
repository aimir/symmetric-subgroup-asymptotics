import SymmetricSubgroupAsymptotics.CFSGTwistedA2TraceFibers

/-! Quadratic-extension trace infrastructure WITHOUT the rank-two q>=3
restriction. A nonfixed element exists by the actual field cardinalities;
its Frobenius difference supplies a nonzero skew parameter also at q=2.
This supports the central A2 block in higher-rank unitary upper arrays. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAQuadraticTrace
open CFSGSerreOrdinaryTwists CFSGTwistedANaturalMatrices
open CFSGTwistedA2FixedField CFSGTwistedA2TraceFibers

theorem order_two_le (q : CFSG.PrimePower) : 2 ≤ q.order :=
  q.prime_isPrime.two_le.trans (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)

theorem exists_nonfixed (q : CFSG.PrimePower) :
    ∃ x : q.Extension 2, definingFieldAutomorphism q 2 x ≠ x := by
  classical
  by_contra hn
  have hall (x : q.Extension 2) : definingFieldAutomorphism q 2 x = x := by
    by_contra hx
    exact hn ⟨x, hx⟩
  let f : q.Extension 2 → fixedField q := fun x => ⟨x, hall x⟩
  have hf : Function.Injective f := by
    intro x y h
    exact congrArg (fun a : fixedField q => a.val) h
  have hc := Nat.card_le_card_of_injective f hf
  rw [extension_two_card, fixedField_card] at hc
  have hq := order_two_le q
  nlinarith

theorem exists_skew_nonzero (q : CFSG.PrimePower) :
    ∃ t : q.Extension 2, t ≠ 0 ∧ definingFieldAutomorphism q 2 t = -t := by
  obtain ⟨x, hx⟩ := exists_nonfixed q
  refine ⟨x - definingFieldAutomorphism q 2 x, sub_ne_zero.mpr hx.symm, ?_⟩
  rw [map_sub]
  have hs : definingFieldAutomorphism q 2 (definingFieldAutomorphism q 2 x) = x :=
    extension_two_pow_twice q x
  rw [hs]
  ring

theorem trace_kernel_card (q : CFSG.PrimePower) : Nat.card (traceHom q).ker = q.order := by
  obtain ⟨t, ht, hts⟩ := exists_skew_nonzero q
  exact (Nat.card_congr (traceKernelEquivFixed q t ht hts)).trans (fixedField_card q)

theorem trace_range_card (q : CFSG.PrimePower) : Nat.card (traceHom q).range = q.order := by
  have hc := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (traceHom q).ker
  rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivRange (traceHom q)).toEquiv,
    trace_kernel_card q, extension_two_card, pow_two] at hc
  have hq := order_two_le q
  exact mul_right_cancel₀ (by omega : q.order ≠ 0) hc.symm

theorem rangeToFixed_surjective (q : CFSG.PrimePower) :
    Function.Surjective (rangeToFixed q) := by
  exact ((rangeToFixed_injective q).bijective_of_nat_card_le (by
    rw [trace_range_card q, fixedField_card])).surjective

theorem exists_trace_eq_fixed (q : CFSG.PrimePower) (c : q.Extension 2)
    (hc : definingFieldAutomorphism q 2 c = c) :
    ∃ b : q.Extension 2, b + definingFieldAutomorphism q 2 b = c := by
  obtain ⟨x, hx⟩ := rangeToFixed_surjective q ⟨c, hc⟩
  obtain ⟨b, hb⟩ := x.property
  exact ⟨b, hb.trans (congrArg (fun y : fixedField q => y.val) hx)⟩

theorem exists_trace_eq_norm (q : CFSG.PrimePower) (a : q.Extension 2) :
    ∃ b : q.Extension 2,
      b + definingFieldAutomorphism q 2 b = a * definingFieldAutomorphism q 2 a := by
  apply exists_trace_eq_fixed
  rw [map_mul]
  have hs : definingFieldAutomorphism q 2 (definingFieldAutomorphism q 2 a) = a :=
    extension_two_pow_twice q a
  rw [hs, mul_comm]

end SymmetricSubgroupAsymptotics.CFSGTwistedAQuadraticTrace
