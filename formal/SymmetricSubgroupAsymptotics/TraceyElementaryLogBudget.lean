import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Real.Sqrt
import Mathlib.Order.Interval.Finset.Nat

/-! Elementary arithmetic connecting all retained prime-power ceilings to
the logarithmic ceiling. Only the exact characteristic-primary exponent
and a bound on the other prime powers are used. -/
set_option autoImplicit false
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.TraceyElementaryLogBudget

theorem succ_le_two_pow (n : ℕ) : n+1≤2^n := by
  induction n with
  | zero => decide
  | succ n ih => rw [pow_succ];omega

theorem degree_le_two_pow_budget (p s v : ℕ) (hp : 1≤p) (hs : s≠0)
    (hv : 1≤v)
    (hpower : ∀ q ∈ s.primeFactors, q≠p → q^s.factorization q≤v) :
    s≤2^((p-1)*s.factorization p+v^2) := by
  let T := s.primeFactors.erase p
  have hcard : T.card≤v := by
    have hsub : T⊆Finset.Icc 1 v := by
      intro q hq
      have hqS : q∈s.primeFactors := Finset.mem_of_mem_erase hq
      have hqprime := Nat.prime_of_mem_primeFactors hqS
      have he : 1≤s.factorization q := by
        have : s.factorization q≠0 := by
          exact Finsupp.mem_support_iff.mp hqS
        omega
      have hqp : q≠p := (Finset.mem_erase.mp hq).1
      have hqpow : q≤q^s.factorization q := by
        simpa only [pow_one] using Nat.pow_le_pow_right hqprime.pos he
      exact Finset.mem_Icc.mpr ⟨hqprime.pos,hqpow.trans (hpower q hqS hqp)⟩
    simpa using Finset.card_le_card hsub
  have hprod : (∏ q ∈ s.primeFactors, q^s.factorization q)=s := by
    exact Nat.prod_factorization_pow_eq_self hs
  have hsplit : p^s.factorization p*(∏ q ∈ T,q^s.factorization q)=s := by
    by_cases hpm : p∈s.primeFactors
    · exact (Finset.mul_prod_erase s.primeFactors (fun q => q^s.factorization q) hpm).trans hprod
    · have he : s.factorization p=0 := by
        by_contra hne
        exact hpm (Finsupp.mem_support_iff.mpr hne)
      simpa only [he,pow_zero,one_mul,T,Finset.erase_eq_self.mpr hpm] using hprod
  have hT : (∏ q ∈ T,q^s.factorization q)≤v^v := by
    calc
      _ ≤ ∏ _q ∈ T,v := Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun q hq =>
        hpower q (Finset.mem_of_mem_erase hq) (Finset.mem_erase.mp hq).1)
      _ = v^T.card := by simp
      _ ≤ v^v := Nat.pow_le_pow_right hv hcard
  have hpbound : p≤2^(p-1) := by
    have hh := succ_le_two_pow (p-1)
    omega
  have hvbound : v≤2^v := (Nat.le_succ v).trans (succ_le_two_pow v)
  calc
    s = p^s.factorization p*(∏ q ∈ T,q^s.factorization q) := hsplit.symm
    _ ≤ (2^(p-1))^s.factorization p*v^v :=
      Nat.mul_le_mul (Nat.pow_le_pow_left hpbound _) hT
    _ ≤ (2^(p-1))^s.factorization p*(2^v)^v :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hvbound _)
    _ = 2^((p-1)*s.factorization p+v^2) := by rw [←pow_mul,←pow_mul,←pow_add];congr 1;ring

theorem log_budget (p s v : ℕ) (hp : 1≤p) (hs : s≠0) (hv : 1≤v)
    (hpower : ∀ q ∈ s.primeFactors, q≠p → q^s.factorization q≤v) :
    Real.logb 2 (s : ℝ)≤((p-1)*s.factorization p : ℕ)+(v : ℝ)^2 := by
  have hb := degree_le_two_pow_budget p s v hp hs hv hpower
  have hbr : (s : ℝ)≤(2 : ℝ)^((p-1)*s.factorization p+v^2) := by exact_mod_cast hb
  have hsreal : (0 : ℝ)<(s : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hs
  have hl := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ)<2) hsreal hbr
  rw [Real.logb_pow,Real.logb_self_eq_one (by norm_num),mul_one] at hl
  simpa only [Nat.cast_add,Nat.cast_pow] using hl

theorem cap_le_logarithmic (H A u v L : ℝ)
    (hH : 0≤H) (hA : 0≤A) (hv : 0≤v) (hL : 0<L)
    (hbudget : L≤u+v^2) (hprimary : H^2*u≤2*A^2/3)
    (hother : H*v≤A) : H≤2*A/Real.sqrt L := by
  have hs : (H*v)^2≤A^2 := (sq_le_sq₀ (mul_nonneg hH hv) hA).mpr hother
  have hb := mul_le_mul_of_nonneg_left hbudget (sq_nonneg H)
  have hcap : H^2*L≤4*A^2 := by nlinarith
  have hsqrt := Real.sq_sqrt hL.le
  have hmul : H*Real.sqrt L≤2*A := by nlinarith [Real.sqrt_nonneg L]
  exact (le_div_iff₀ (Real.sqrt_pos.mpr hL)).mpr hmul

/-- An actual largest prime-to-characteristic prime power exists, with the
value one exactly the harmless empty-support fallback. -/
theorem exists_largest_other_power (p s : ℕ) :
    ∃ v : ℕ, 1≤v ∧
      (∀ q ∈ s.primeFactors, q≠p → q^s.factorization q≤v) ∧
      (v=1 ∨ ∃ q ∈ s.primeFactors, q≠p ∧ v=q^s.factorization q) := by
  classical
  let T := s.primeFactors.erase p
  by_cases ht : T.Nonempty
  · obtain ⟨q,hq,hmax⟩ := Finset.exists_max_image T (fun q => q^s.factorization q) ht
    have hprime := Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hq)
    refine ⟨q^s.factorization q,Nat.one_le_pow _ _ hprime.pos,?_,?_⟩
    · intro r hr hrp
      exact hmax r (Finset.mem_erase.mpr ⟨hrp,hr⟩)
    · exact Or.inr ⟨q,Finset.mem_of_mem_erase hq,(Finset.mem_erase.mp hq).1,rfl⟩
  · refine ⟨1,le_rfl,?_,Or.inl rfl⟩
    intro q hq hqp
    exact (ht ⟨q,Finset.mem_erase.mpr ⟨hqp,hq⟩⟩).elim

end SymmetricSubgroupAsymptotics.TraceyElementaryLogBudget
