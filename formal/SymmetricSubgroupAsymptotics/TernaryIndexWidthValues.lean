import SymmetricSubgroupAsymptotics.InducedTernaryWidthEnvelope

/-! Literal small values of the canonical integer ternary width envelope.
These are coefficient identities; no classification of top groups is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

@[simp] theorem ternaryIndexWidth_two : ternaryIndexWidth 2 = 1 :=
  ternaryWidthEnvelope_two (ternaryIndexWidth_factors 2 (by decide))

@[simp] theorem ternaryIndexWidth_three : ternaryIndexWidth 3 = 1 := by
  have hf : (3 : ℕ).factorization 3 = 1 := Nat.prime_three.factorization_self
  norm_num [ternaryIndexWidth, ternaryWidthEnvelope, ternaryWidthCore, hf,
    largestPrimePower]

@[simp] theorem ternaryIndexWidth_four : ternaryIndexWidth 4 = 1 := by
  have hf : (4 : ℕ).factorization 3 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by decide)
  have hfactor : (4 : ℕ).factorization = Finsupp.single 2 2 := by
    simpa using Nat.prime_two.factorization_pow (k := 2)
  have hl : largestPrimePower 4 = 4 := by
    norm_num [largestPrimePower, hfactor]
  norm_num [ternaryIndexWidth, ternaryWidthEnvelope, ternaryWidthCore, hf, hl]

@[simp] theorem ternaryIndexWidth_six : ternaryIndexWidth 6 = 2 :=
  ternaryWidthEnvelope_six (ternaryIndexWidth_factors 6 (by decide))

@[simp] theorem ternaryIndexWidth_nine : ternaryIndexWidth 9 = 3 := by
  have hf : (9 : ℕ).factorization 3 = 2 := by
    simpa using Nat.factorization_pow_self Nat.prime_three (n := 2)
  norm_num [ternaryIndexWidth, ternaryWidthEnvelope, ternaryWidthCore, hf,
    largestPrimePower]

@[simp] theorem ternaryIndexWidth_eighteen : ternaryIndexWidth 18 = 6 :=
  ternaryWidthEnvelope_eighteen (ternaryIndexWidth_factors 18 (by decide))

end SymmetricSubgroupAsymptotics
