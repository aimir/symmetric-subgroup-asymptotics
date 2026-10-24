import SymmetricSubgroupAsymptotics.PrimitiveSocleClassicalClassEquationCapacity

/-! Small arithmetic applications of the shared class-equation test.
Prime field orders force extension degree one from the literal
prime-power equation; the displayed integer inequalities are checked by
the kernel. This is not a subgroup or action census. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.ClassicalClassEquationCapacity

theorem exponent_eq_one_of_prime_order (q : CFSG.PrimePower)
    (hp : Nat.Prime q.order) : q.exponent = 1 :=
  (Nat.Prime.pow_inj' q.prime_isPrime hp q.exponent_pos.ne'
    (by decide : (1 : ℕ) ≠ 0)
    (show q.prime^q.exponent = q.order^1 from by rw [pow_one]; rfl)).2

theorem typeB_small (r : ℕ) (q : CFSG.PrimePower)
    (h : (r = 3 ∧ (q.order = 11 ∨ q.order = 13)) ∨ (r = 9 ∧ q.order = 2)) :
    typeB r q := by
  have he : q.exponent = 1 := exponent_eq_one_of_prime_order q (by
    rcases h with ⟨_, hq | hq⟩ | ⟨_, hq⟩ <;> rw [hq] <;> decide)
  rcases h with ⟨rfl, hq | hq⟩ | ⟨rfl, hq⟩ <;>
    simp only [typeB, hq, he] <;> decide

theorem typeD_small (r : ℕ) (q : CFSG.PrimePower)
    (h : (r = 4 ∧ q.order = 5) ∨ (r = 9 ∧ q.order = 2)) : typeD r q := by
  have he : q.exponent = 1 := exponent_eq_one_of_prime_order q (by
    rcases h with ⟨_, hq⟩ | ⟨_, hq⟩ <;> rw [hq] <;> decide)
  rcases h with ⟨rfl, hq⟩ | ⟨rfl, hq⟩ <;> simp only [typeD, hq, he] <;> decide

theorem unitary_rank_two_seven (q : CFSG.PrimePower) (hq : q.order = 7) :
    unitary 2 q := by
  have he := exponent_eq_one_of_prime_order q (by rw [hq]; decide)
  simp only [unitary, hq, he]
  decide

end SymmetricSubgroupAsymptotics.ClassicalClassEquationCapacity
