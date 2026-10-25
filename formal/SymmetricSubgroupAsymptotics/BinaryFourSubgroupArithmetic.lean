import SymmetricSubgroupAsymptotics.FiniteGroupPrimeMultiplicityGenerators
import Mathlib.NumberTheory.Divisors

/-! Small scalar certificates for divisors of the genuine GL4(F2) order.
These are statements about integer divisors, not a subgroup catalogue. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.BinaryFourSubgroupArithmetic

private theorem divisor_certificate :
    ∀ h ∈ Nat.divisors 20160, 8 * h ≤ 20160 →
      ArithmeticFunction.cardFactors h ≤ 8 ∧
        (ArithmeticFunction.cardFactors h ≤ 7 ∨ 32 ∣ h) := by
  decide +kernel

theorem budget {h k : ℕ} (hmul : h * k = 20160) (hk : 8 ≤ k) :
    ArithmeticFunction.cardFactors h ≤ 8 ∧
      (ArithmeticFunction.cardFactors h ≤ 7 ∨ 32 ∣ h) := by
  have hd : h ∈ Nat.divisors 20160 :=
    Nat.mem_divisors.mpr ⟨⟨k,hmul.symm⟩,by decide⟩
  exact divisor_certificate h hd (by nlinarith)

theorem factorial_lt {k : ℕ} (hk : k < 8) : k.factorial < 20160 := by
  have hle : k.factorial ≤ Nat.factorial 7 := Nat.factorial_le (by omega)
  norm_num at hle ⊢
  omega

end SymmetricSubgroupAsymptotics.BinaryFourSubgroupArithmetic
