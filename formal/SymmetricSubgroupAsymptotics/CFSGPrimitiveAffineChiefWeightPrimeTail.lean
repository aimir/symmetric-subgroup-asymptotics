import SymmetricSubgroupAsymptotics.CFSGPrimitiveChiefWeightOrderBounds

/-! Prime-degree affine actual ternary chief weights are paid by the actual
one-dimensional complement, without any composition-length input. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveAffineProfile
open CFSGPrimitiveTernaryTailNumerics

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [Nontrivial X]

theorem chiefThreeWeight_le_log2_of_degree_prime (P : PrimitiveAffineProfile G X)
    (hp : MulAction.IsPreprimitive G X) (hprime : (Nat.card X).Prime)
    (hf : 34 ≤ Nat.card X) (c : ActualChiefSeries G) :
    actualChiefSeriesTernaryWeight c ≤ Nat.log2 (Nat.card X) := by
  obtain ⟨p,d,hp',hd,he,hdiv,hne⟩ := P.exists_prime_dimension_order_divisor hp
  have hd1 : d=1 :=
    (prime_pow_positive_injective hp' hprime hd (by decide)
      (by simpa only [pow_one] using he.symm)).2
  rw [hd1] at hdiv hne
  have hep : Nat.card X=p := by simpa only [hd1,pow_one] using he
  have hp34 : 34 ≤ p := by omega
  have hvp : p.factorization 3=0 := by
    by_contra h
    have hh := hp'.eq_of_factorization_pos h
    omega
  have hfull : fullAffineOrder p 1=p*(p-1) := by
    simp [fullAffineOrder,fullLinearOrder]
  have hvfull : (fullAffineOrder p 1).factorization 3=(p-1).factorization 3 := by
    rw [hfull,Nat.factorization_mul hp'.ne_zero (by omega)]
    change p.factorization 3 + (p-1).factorization 3 = (p-1).factorization 3
    rw [hvp,zero_add]
  have hv := (Nat.factorization_le_iff_dvd Nat.card_pos.ne' hne).2 hdiv 3
  rw [hvfull] at hv
  have hh := (actualChiefSeriesTernaryWeight_le_order c).trans hv
  refine hh.trans ?_
  rw [hep]
  have hm := ternary_factorization_le_log2 (p-1) (by omega)
  have hl : Nat.log2 (p-1) ≤ Nat.log2 p := by
    simp only [Nat.log2_eq_log_two]
    exact Nat.log_mono_right (Nat.sub_le p 1)
  exact hm.trans hl

theorem chiefThreeWeight_strict_prime_tail (P : PrimitiveAffineProfile G X)
    (hp : MulAction.IsPreprimitive G X) (hprime : (Nat.card X).Prime)
    (hf : 34 ≤ Nat.card X) (c : ActualChiefSeries G) :
    20*actualChiefSeriesTernaryWeight c < 3*Nat.card X :=
  (Nat.mul_le_mul_left 20 (P.chiefThreeWeight_le_log2_of_degree_prime hp hprime hf c)).trans_lt
    (c1_primitive_log_tail (Nat.card X) hf)

end SymmetricSubgroupAsymptotics.PrimitiveAffineProfile
