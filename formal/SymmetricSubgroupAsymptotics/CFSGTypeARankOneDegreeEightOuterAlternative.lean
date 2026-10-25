import SymmetricSubgroupAsymptotics.CFSGTypeASmallDegreeOuterBudget

/-! For actual PSL2 with least proper index at most eight, the outer
ORDER is at most three, except for the literal order360 model where its
order is at most four. No model identification or action catalogue is
used: field-size/index bounds retain the actual rank-one source. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTypeARankOneDegreeEightOuterAlternative
open PrimitiveSocleRawStructure

theorem outer_le_three_or_order_three_sixty (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.A 1 q)] (ell : ℕ)
    (hell : LeastProperIndex (CFSG.Models.A 1 q) ell) (hsmall : ell ≤ 8) :
    Nat.card (Outer (CFSG.Models.A 1 q)) ≤ 3 ∨
      (Nat.card (CFSG.Models.A 1 q) = 360 ∧
        Nat.card (Outer (CFSG.Models.A 1 q)) ≤ 4) := by
  by_cases hp : q.prime = 2
  · have hc : ringChar q.Field = 2 := (ringChar.eq q.Field q.prime).trans hp
    have hi := CFSGPSLTwoEvenPermutationDegree.field_card_le_leastProperIndex
      (F := q.Field) hc ell hell
    rw [q.card_field] at hi
    have he : q.exponent ≤ 3 := by
      by_contra h
      have hb := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 4 ≤ q.exponent)
      have hq : q.order = 2^q.exponent := by simp only [CFSG.PrimePower.order,hp]
      have h16 : 16 ≤ q.order := by simpa only [hq] using hb
      omega
    exact Or.inl ((CFSGPSLTwoEvenOuterBound.typeA_rank_one_outer_card q hp).trans he)
  · have hi := CFSGPSLTwoGeometry.field_card_le_twice_leastProperIndex
      (F := q.Field) ell hell
    rw [q.card_field] at hi
    have hq : q.order ≤ 16 := by omega
    have hp3 : 3 ≤ q.prime := by have hh := q.prime_isPrime.two_le; omega
    have he : q.exponent ≤ 2 := by
      by_contra h
      have hb := (Nat.pow_le_pow_left hp3 3).trans
        (Nat.pow_le_pow_right q.prime_isPrime.pos (by omega : 3 ≤ q.exponent))
      have h27 : 27 ≤ q.order := hb
      omega
    by_cases he1 : q.exponent = 1
    · have ho := CFSGPSLTwoOuterBound.typeA_rank_one_outer_card q
      exact Or.inl (by omega)
    · have he2 : q.exponent = 2 := by have hh := q.exponent_pos; omega
      have hp5 : q.prime < 5 := by
        by_contra h
        have hb := Nat.pow_le_pow_left (by omega : 5 ≤ q.prime) 2
        have hqpow : q.order = q.prime^2 := by simp only [CFSG.PrimePower.order,he2]
        have h25 : 25 ≤ q.order := by simpa only [hqpow] using hb
        omega
      have hp_eq : q.prime = 3 := by
        have hcases : q.prime = 3 ∨ q.prime = 4 := by omega
        rcases hcases with h | h
        · exact h
        · have hprime := q.prime_isPrime
          norm_num only [h] at hprime
      have h9 : q.order = 9 := by simp only [CFSG.PrimePower.order,hp_eq,he2]; decide
      exact Or.inr ⟨CFSGTypeARankOneCardNine.card_eq q h9,
        CFSGTypeARankOneCardNine.outer_card_le q h9⟩

end SymmetricSubgroupAsymptotics.CFSGTypeARankOneDegreeEightOuterAlternative
