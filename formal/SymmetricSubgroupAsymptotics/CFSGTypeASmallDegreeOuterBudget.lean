import SymmetricSubgroupAsymptotics.CFSGTypeAOuterGcdCardinality
import SymmetricSubgroupAsymptotics.CFSGTypeAMinimumIndexLower
import SymmetricSubgroupAsymptotics.CFSGPSLTwoEvenOuterBound
import SymmetricSubgroupAsymptotics.CFSGPSLTwoEvenPermutationDegree
import SymmetricSubgroupAsymptotics.CFSGTypeARankOneCardNine

/-! Uniform actual outer budgets for original type A in permutation
degrees at most ten. The only larger outer order below degree eight is
the literal nine-element-field PSL2 model, whose proved order360 is
retained for the SAME-action quotient calculation. No exceptional-model
identification, group catalogue or global permutation bound is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTypeASmallDegreeOuterBudget
open PrimitiveSocleRawStructure

private theorem prime_le_order (q : CFSG.PrimePower) : q.prime ≤ q.order := by
  simpa only [pow_one] using
    (Nat.pow_le_pow_right q.prime_isPrime.pos (show 1 ≤ q.exponent from q.exponent_pos))

private theorem odd_exponent_le_two (q : CFSG.PrimePower) (hp : q.prime ≠ 2)
    (hq : q.order ≤ 20) : q.exponent ≤ 2 := by
  have hp3 : 3 ≤ q.prime := by have hh := q.prime_isPrime.two_le; omega
  by_contra he
  have hpow := (Nat.pow_le_pow_left hp3 3).trans
    (Nat.pow_le_pow_right q.prime_isPrime.pos (by omega : 3 ≤ q.exponent))
  change 27 ≤ q.order at hpow
  omega

private theorem binary_exponent_le (q : CFSG.PrimePower) (hp : q.prime = 2)
    (k : ℕ) (hq : q.order < 2^(k+1)) : q.exponent ≤ k := by
  by_contra he
  have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : k+1 ≤ q.exponent)
  have hq' : q.order = 2^q.exponent := by simp only [CFSG.PrimePower.order,hp]
  omega

theorem rank_one_outer_card_le_four (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.A 1 q)] (ell : ℕ)
    (hell : LeastProperIndex (CFSG.Models.A 1 q) ell) (hsmall : ell ≤ 10) :
    Nat.card (Outer (CFSG.Models.A 1 q)) ≤ 4 := by
  by_cases hp : q.prime = 2
  · have hc : ringChar q.Field = 2 := (ringChar.eq q.Field q.prime).trans hp
    have hi := CFSGPSLTwoEvenPermutationDegree.field_card_le_leastProperIndex (F := q.Field)
      hc ell hell
    rw [q.card_field] at hi
    have he := binary_exponent_le q hp 3 (by omega : q.order < 2^(3+1))
    exact (CFSGPSLTwoEvenOuterBound.typeA_rank_one_outer_card q hp).trans (by omega)
  · have hi := CFSGPSLTwoGeometry.field_card_le_twice_leastProperIndex (F := q.Field) ell hell
    rw [q.card_field] at hi
    have he := odd_exponent_le_two q hp (by omega)
    have ho := CFSGPSLTwoOuterBound.typeA_rank_one_outer_card q
    omega

theorem rank_one_outer_le_two_or_order_three_sixty (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.A 1 q)] (ell : ℕ)
    (hell : LeastProperIndex (CFSG.Models.A 1 q) ell) (hsmall : ell ≤ 7) :
    Nat.card (Outer (CFSG.Models.A 1 q)) ≤ 2 ∨
      (Nat.card (CFSG.Models.A 1 q) = 360 ∧ Nat.card (Outer (CFSG.Models.A 1 q)) ≤ 4) := by
  by_cases hp : q.prime = 2
  · have hc : ringChar q.Field = 2 := (ringChar.eq q.Field q.prime).trans hp
    have hi := CFSGPSLTwoEvenPermutationDegree.field_card_le_leastProperIndex (F := q.Field)
      hc ell hell
    rw [q.card_field] at hi
    have he := binary_exponent_le q hp 2 (by omega : q.order < 2^(2+1))
    exact Or.inl ((CFSGPSLTwoEvenOuterBound.typeA_rank_one_outer_card q hp).trans he)
  · have hi := CFSGPSLTwoGeometry.field_card_le_twice_leastProperIndex (F := q.Field) ell hell
    rw [q.card_field] at hi
    have hq : q.order ≤ 14 := by omega
    have he := odd_exponent_le_two q hp (by omega)
    by_cases he1 : q.exponent = 1
    · have ho := CFSGPSLTwoOuterBound.typeA_rank_one_outer_card q
      exact Or.inl (by omega)
    · have he2 : q.exponent = 2 := by have hh := q.exponent_pos; omega
      have hp3 : 3 ≤ q.prime := by have hh := q.prime_isPrime.two_le; omega
      have hpless : q.prime < 4 := by
        by_contra hh
        have hb := Nat.pow_le_pow_left (by omega : 4 ≤ q.prime) 2
        have hqpow : q.order = q.prime^2 := by simp only [CFSG.PrimePower.order,he2]
        rw [← hqpow] at hb
        norm_num at hb
        omega
      have hp_eq : q.prime = 3 := by omega
      have h9 : q.order = 9 := by simp only [CFSG.PrimePower.order,hp_eq,he2]; decide
      exact Or.inr ⟨CFSGTypeARankOneCardNine.card_eq q h9,
        CFSGTypeARankOneCardNine.outer_card_le q h9⟩

theorem higher_outer_card_le_two (r : ℕ) (hr : 2 ≤ r) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.A r q)] (ell : ℕ)
    (hell : LeastProperIndex (CFSG.Models.A r q) ell) (hsmall : ell ≤ 10) :
    Nat.card (Outer (CFSG.Models.A r q)) ≤ 2 := by
  have hi := CFSGTypeAMinimumIndexLower.order_power_le_leastProperIndex r hr q ell hell
  have hq2 : 2 ≤ q.order := q.prime_isPrime.two_le.trans (prime_le_order q)
  have hr4 : r < 4 := by
    by_contra hh
    have hb := (Nat.pow_le_pow_left hq2 4).trans
      (Nat.pow_le_pow_right (by omega) (by omega : 4 ≤ r))
    norm_num at hb
    omega
  have hq4 : q.order < 4 := by
    by_contra hh
    have hb := (Nat.pow_le_pow_left (by omega : 4 ≤ q.order) 2).trans
      (Nat.pow_le_pow_right (by omega) hr)
    norm_num at hb
    omega
  have he : q.exponent = 1 := by
    by_contra hh
    have hexp : 2 ≤ q.exponent := by have hpos := q.exponent_pos; omega
    have hb := (Nat.pow_le_pow_left q.prime_isPrime.two_le 2).trans
      (Nat.pow_le_pow_right q.prime_isPrime.pos hexp)
    change 4 ≤ q.order at hb
    omega
  have hgcd : (q.order-1).gcd (r+1) = 1 := by
    have hc : q.order = 2 ∨ q.order = 3 := by omega
    rcases hc with hq | hq
    · simp only [hq,Nat.reduceSub,Nat.gcd_one_left]
    · have hr2 : r = 2 := by
        by_contra hh
        have h3 : r = 3 := by omega
        have hb : 27 ≤ ell := by simpa only [hq,h3] using hi
        omega
      norm_num [hq,hr2]
  have ho := CFSGTypeAOuterGcdCardinality.typeA_higher_outer_card_le_gcd r hr q
  simpa only [hgcd,he,mul_one] using ho

end SymmetricSubgroupAsymptotics.CFSGTypeASmallDegreeOuterBudget
