import SymmetricSubgroupAsymptotics.FiniteGroupPrimeMultiplicityGenerators
import SymmetricSubgroupAsymptotics.MarkedC4AbelianSectionSize
import SymmetricSubgroupAsymptotics.PrimeGeneralLinearDefiningValuation
import Mathlib.Algebra.BigOperators.Fin

/-! Uniform prime-multiplicity bounds for the ACTUAL binary GL order.
Every order factor consumes at most d-1 primes, so translation dimension
plus the complement's total prime charge is at most d squared. No matrix
subgroup classification or ordinary simple-generation input is used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.BinaryGeneralLinearTotalPrimeMultiplicity

private theorem cardFactors_prod {ι : Type*} (s : Finset ι) (f : ι → ℕ)
    (hn : ∀ i ∈ s, f i ≠ 0) :
    ArithmeticFunction.cardFactors (∏ i ∈ s, f i) =
      ∑ i ∈ s, ArithmeticFunction.cardFactors (f i) := by
  revert hn
  induction s using Finset.induction_on with
  | empty => intro hn; simp
  | @insert a s ha ih =>
      intro hn
      have hfa : f a ≠ 0 := hn a (Finset.mem_insert_self _ _)
      have hs : ∀ i ∈ s, f i ≠ 0 := fun i hi => hn i (Finset.mem_insert_of_mem hi)
      rw [Finset.prod_insert ha,ArithmeticFunction.cardFactors_mul hfa
        (Finset.prod_ne_zero_iff.mpr hs),ih hs,Finset.sum_insert ha]

theorem power_sub_one_cardFactors_le (k : ℕ) (hk : 0 < k) :
    ArithmeticFunction.cardFactors (2^k-1) ≤ k-1 := by
  have hpow : 1 < (2 : ℕ)^k := Nat.one_lt_pow (Nat.ne_of_gt hk) (by decide)
  have hn : 2^k-1 ≠ 0 := by omega
  have hh : 2^ArithmeticFunction.cardFactors (2^k-1) ≤ 2^k-1 := by
    simpa only [ArithmeticFunction.cardFactors_apply,MarkedC4.AbelianSectionSize.omega]
      using MarkedC4.AbelianSectionSize.two_pow_omega_le hn
  have hlt : 2^ArithmeticFunction.cardFactors (2^k-1) < (2 : ℕ)^k :=
    hh.trans_lt (by omega)
  have he : ArithmeticFunction.cardFactors (2^k-1) < k :=
    (Nat.pow_lt_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hlt
  omega

theorem power_difference_cardFactors_le (d i : ℕ) (hi : i < d) :
    ArithmeticFunction.cardFactors (2^d-2^i) ≤ d-1 := by
  have hk : 0 < d-i := by omega
  have hn : 2^(d-i)-1 ≠ 0 := by
    have hh : 1 < (2 : ℕ)^(d-i) := Nat.one_lt_pow (by omega) (by decide)
    omega
  have hmul : 2^d-2^i = 2^i*(2^(d-i)-1) := by
    rw [Nat.mul_sub_left_distrib,mul_one,←pow_add,show i+(d-i)=d by omega]
  rw [hmul,ArithmeticFunction.cardFactors_mul (by positivity : (2 : ℕ)^i ≠ 0) hn,
    ArithmeticFunction.cardFactors_apply_prime_pow Nat.prime_two]
  have hh := power_sub_one_cardFactors_le (d-i) hk
  omega

theorem GL_cardFactors_le (d : ℕ) :
    ArithmeticFunction.cardFactors
      (Nat.card (Matrix.GeneralLinearGroup (Fin d) (ZMod 2))) ≤ d*(d-1) := by
  have he : Nat.card (Matrix.GeneralLinearGroup (Fin d) (ZMod 2)) =
      ∏ i : Fin d, (2^d-2^(i : ℕ)) := by
    simpa only [Fintype.card_eq_nat_card,Nat.card_zmod] using
      (Matrix.card_GL_field (𝔽 := ZMod 2) d)
  have hn : ∀ i : Fin d, 2^d-2^(i : ℕ) ≠ 0 := fun i =>
    Nat.sub_ne_zero_of_lt (Nat.pow_lt_pow_right (by decide : 1 < (2 : ℕ)) i.isLt)
  rw [he,cardFactors_prod Finset.univ _ (fun i _ => hn i)]
  calc
    _ ≤ ∑ _i : Fin d, (d-1) := Finset.sum_le_sum (fun i _ =>
      power_difference_cardFactors_le d i i.isLt)
    _ = d*(d-1) := by simp

theorem dimension_add_GL_cardFactors_le_sq (d : ℕ) :
    d + ArithmeticFunction.cardFactors
      (Nat.card (Matrix.GeneralLinearGroup (Fin d) (ZMod 2))) ≤ d^2 := by
  have hh := GL_cardFactors_le d
  by_cases hd : d = 0
  · simpa only [hd,zero_mul,zero_add,pow_two,mul_zero] using hh
  · have he : d-1+1 = d := Nat.sub_add_cancel (by omega)
    nlinarith

end SymmetricSubgroupAsymptotics.BinaryGeneralLinearTotalPrimeMultiplicity
