import SymmetricSubgroupAsymptotics.BinaryPermutationOrder
import Mathlib.Tactic

/-! Primes at least five satisfy the required class bound already by
actual permutation-group order. The same original degree pays the full order. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.LargePrimePermutationClassFourthBound

private theorem prime_fourth_le (p : ℕ) (hp : 5 ≤ p) : p ^ 4 ≤ 5 ^ (p - 1) := by
  have hlarge : ∀ k : ℕ, (k + 5) ^ 4 ≤ 5 ^ (k + 4) := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih =>
      calc
        (k.succ + 5)^4 ≤ 5*(k+5)^4 := by
          have h2 := Nat.zero_le (k^2)
          have h3 := Nat.zero_le (k^3)
          have h4 := Nat.zero_le (k^4)
          simp only [Nat.succ_eq_add_one]
          nlinarith
        _ ≤ 5 * 5^(k+4) := Nat.mul_le_mul_left 5 ih
        _ = _ := by
          rw [show k.succ + 4 = (k+4)+1 by omega, pow_succ]
          exact Nat.mul_comm _ _
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hp
  rw [show 5+k-1=k+4 by omega, show 5+k=k+5 by omega]
  exact hlarge k

/-- Full actual group order bound, before any conjugacy-class quotient. -/
theorem pGroup_card_le (p : ℕ) [Fact p.Prime]
    (G X : Type) [Group G] [Finite G] [Finite X]
    [MulAction G X] [FaithfulSMul G X] (hG : IsPGroup p G) :
    Nat.card G ≤ p ^ (Nat.card X / (p-1)) := by
  let f : G →* Equiv.Perm X := MulAction.toPermHom G X
  let e : G ≃* f.range := MonoidHom.ofInjective
    (show Function.Injective f from MulAction.toPerm_injective)
  obtain ⟨P,hP⟩ := (hG.of_equiv e).exists_le_sylow
  have hord : Nat.card G ≤ Nat.card P := by
    rw [Nat.card_congr e.toEquiv]
    exact Nat.card_le_card_of_injective (Subgroup.inclusion hP)
      (Subgroup.inclusion_injective hP)
  calc
    Nat.card G ≤ Nat.card P := hord
    _ = p ^ ((Nat.factorial (Nat.card X)).factorization p) := by
      rw [P.card_eq_multiplicity, Nat.card_perm]
    _ ≤ p ^ (Nat.card X / (p-1)) := Nat.pow_le_pow_right
      (Fact.out : p.Prime).pos (Nat.factorization_factorial_le_div_pred
        (Fact.out : p.Prime) (Nat.card X))

/-- The actual fourth-power class bound, with no class-number assumption. -/
theorem class_card_pow_four_le (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (G X : Type) [Group G] [Finite G] [Finite X]
    [MulAction G X] [FaithfulSMul G X] (hG : IsPGroup p G) :
    Nat.card (ConjClasses G)^4 ≤ 5^Nat.card X := by
  have hclass := Nat.card_le_card_of_surjective (@ConjClasses.mk G _) ConjClasses.mk_surjective
  have horder := pGroup_card_le p G X hG
  calc
    _ ≤ (p ^ (Nat.card X / (p-1)))^4 := Nat.pow_le_pow_left (hclass.trans horder) 4
    _ = (p^4)^(Nat.card X / (p-1)) := by simp only [← pow_mul, Nat.mul_comm]
    _ ≤ (5^(p-1))^(Nat.card X / (p-1)) := Nat.pow_le_pow_left (prime_fourth_le p hp) _
    _ = 5^((p-1)*(Nat.card X/(p-1))) := (pow_mul _ _ _).symm
    _ ≤ 5^Nat.card X := Nat.pow_le_pow_right (by decide) (Nat.mul_div_le _ _)

end SymmetricSubgroupAsymptotics.LargePrimePermutationClassFourthBound
