import SymmetricSubgroupAsymptotics.MarkedC4AbelianSectionSize
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-! Exact arithmetic for the original prime-factor-with-multiplicity
section size. In particular every nontrivial finite simple socle row pays
at least one unit per retained copy. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.MarkedC4.AbelianSectionSize

theorem omega_eq_cardFactors (n : ℕ) : omega n = ArithmeticFunction.cardFactors n := rfl

@[simp] theorem omega_one : omega 1 = 0 := by
  rw [omega_eq_cardFactors]
  exact ArithmeticFunction.cardFactors_one

theorem omega_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    omega (m*n) = omega m + omega n :=
  ArithmeticFunction.cardFactors_mul hm hn

theorem omega_pow (n d : ℕ) : omega (n^d) = d * omega n :=
  ArithmeticFunction.cardFactors_pow

theorem omega_pos_iff_one_lt {n : ℕ} : 0 < omega n ↔ 1 < n :=
  ArithmeticFunction.cardFactors_pos_iff_one_lt

theorem omega_prod {I : Type} (s : Finset I) (f : I → ℕ)
    (hf : ∀ i ∈ s, f i ≠ 0) :
    omega (∏ i ∈ s, f i) = ∑ i ∈ s, omega (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have htail : ∀ i ∈ s, f i ≠ 0 := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    rw [Finset.prod_insert ha, omega_mul (hf a (Finset.mem_insert_self a s))
      (Finset.prod_ne_zero_iff.mpr htail), Finset.sum_insert ha, ih htail]

theorem omega_prod_pow {I : Type} (s : Finset I) (f d : I → ℕ)
    (hf : ∀ i ∈ s, f i ≠ 0) :
    omega (∏ i ∈ s, f i ^ d i) = ∑ i ∈ s, d i * omega (f i) := by
  rw [omega_prod s _ (fun i hi => pow_ne_zero _ (hf i hi))]
  exact Finset.sum_congr rfl (fun i _ => omega_pow (f i) (d i))

end SymmetricSubgroupAsymptotics.MarkedC4.AbelianSectionSize
