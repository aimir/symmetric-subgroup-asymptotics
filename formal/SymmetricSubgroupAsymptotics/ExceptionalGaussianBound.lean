import SymmetricSubgroupAsymptotics.ExceptionalLiftKernel

/-!
# Uniform exceptional Gaussian incidence sum

The literal rational Gaussian coefficients are compared with their quadratic
powers. The joint dimension sum is then bounded by the retained-incidence
kernel, with one constant independent of the profile and both parities.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics

/-- A uniform upper bound for every actual binary Gaussian coefficient. -/
theorem binaryGaussianCoefficient_le_quadratic (r k : ℕ) (hk : k ≤ r) :
    (binaryGaussianCoefficient r k : ℝ) ≤
      eulerProduct⁻¹ * (2 : ℝ) ^ (k * (r - k)) := by
  have h := (binaryGaussianCoefficient_normalized_error r k hk).1
  exact (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ (k * (r-k)))).mp
    (sub_nonneg.mp h)

/-- A positive uniform lower bound, including endpoint dimensions. -/
theorem quadratic_le_binaryGaussianCoefficient (r k : ℕ) (hk : k ≤ r) :
    eulerProduct * (2 : ℝ) ^ (k * (r - k)) ≤
      (binaryGaussianCoefficient r k : ℝ) := by
  rw [binaryGaussianCoefficient_euler r k hk]
  have hden : eulerPartialProduct k * eulerPartialProduct (r-k) ≤ 1 :=
    mul_le_one₀ (eulerPartialProduct_le_one k) (eulerPartialProduct_pos (r-k)).le
      (eulerPartialProduct_le_one (r-k))
  have hpos : 0 < eulerPartialProduct k * eulerPartialProduct (r-k) :=
    mul_pos (eulerPartialProduct_pos k) (eulerPartialProduct_pos (r-k))
  apply (le_div_iff₀ hpos).mpr
  calc
    _ ≤ eulerProduct * (2 : ℝ) ^ (k*(r-k)) :=
      mul_le_of_le_one_right (by positivity [euler_positive]) hden
    _ ≤ (2 : ℝ) ^ (k*(r-k)) * eulerPartialProduct r := by
      simpa only [mul_comm] using
        mul_le_mul_of_nonneg_right (eulerProduct_le_partial r) (by positivity : (0 : ℝ) ≤ 2 ^ (k*(r-k)))

/-- The central coefficient already supplies a uniform lower bound on the
explicit total Gaussian sum. The exact parity-sensitive power is retained. -/
theorem quadratic_le_binaryGaussianSum (r : ℕ) :
    eulerProduct * (2 : ℝ) ^ gaussianPower r ≤ (binaryGaussianSum r : ℝ) := by
  calc
    _ ≤ (binaryGaussianCoefficient r (r/2) : ℝ) :=
      quadratic_le_binaryGaussianCoefficient r (r/2) (Nat.div_le_self r 2)
    _ ≤ _ := by
      unfold binaryGaussianSum
      push_cast
      apply Finset.single_le_sum (f := fun k : ℕ ↦ (binaryGaussianCoefficient r k : ℝ))
        (s := Finset.range (r+1)) (a := r/2)
      · intro k hk
        change (0 : ℝ) ≤ (binaryGaussianCoefficient r k : ℝ)
        exact_mod_cast (binaryGaussianCoefficient_pos (r := r) (k := k)
          (by simpa using hk)).le
      · exact Finset.mem_range.mpr (by omega)

/-- The complete numerical incidence sum: every image dimension and every
positive retained relation dimension is included. -/
def exceptionalGaussianSum (R t : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (R+1), (binaryGaussianCoefficient R k : ℝ) *
    ∑ l ∈ Finset.Icc 1 t, (binaryGaussianCoefficient t l : ℝ) * (72 : ℝ)^l /
      (2 : ℝ)^(k*l)

theorem exceptionalGaussianSum_nonneg (R t : ℕ) : 0 ≤ exceptionalGaussianSum R t := by
  apply Finset.sum_nonneg
  intro k hk
  apply mul_nonneg
  · exact_mod_cast (binaryGaussianCoefficient_pos (r := R) (k := k) (by simpa using hk)).le
  · apply Finset.sum_nonneg
    intro l hl
    apply div_nonneg
    · apply mul_nonneg
      · exact_mod_cast (binaryGaussianCoefficient_pos (r := t) (k := l) (Finset.mem_Icc.mp hl).2).le
      · positivity
    · positivity

/-- The natural-power denominator is exactly the incidence exponential,
with the product taken in the reals after casting. -/
theorem exceptionalGaussianSum_eq_rpow (R t : ℕ) :
    exceptionalGaussianSum R t =
      ∑ k ∈ Finset.range (R+1), (binaryGaussianCoefficient R k : ℝ) *
        ∑ l ∈ Finset.Icc 1 t, (binaryGaussianCoefficient t l : ℝ) * (72 : ℝ)^l *
          (2 : ℝ)^(-((k : ℝ)*(l : ℝ))) := by
  have hpow (k l : ℕ) : (2 : ℝ)^(-((k : ℝ)*(l : ℝ))) = ((2 : ℝ)^(k*l))⁻¹ := by
    rw [← Nat.cast_mul,Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),Real.rpow_natCast]
  simp only [exceptionalGaussianSum,hpow,div_eq_mul_inv]

/-- An explicit absolute constant for the entire exceptional sum. -/
def exceptionalGaussianConstant : ℝ :=
  (2 : ℝ) ^ (66 : ℕ) * halfLatticeGaussianSum / eulerProduct^3

theorem exceptionalGaussianConstant_pos : 0 < exceptionalGaussianConstant := by
  unfold exceptionalGaussianConstant
  positivity [halfLatticeGaussianSum_pos,euler_positive]

private theorem exceptionalGaussian_term_le (R t k l : ℕ) (hk : k ≤ R) (hl : l ≤ t) :
    (binaryGaussianCoefficient R k : ℝ) *
        ((binaryGaussianCoefficient t l : ℝ) * (72 : ℝ)^l / (2 : ℝ)^(k*l)) ≤
      (eulerProduct⁻¹)^2 * (2 : ℝ)^gaussianPower R *
        ((72 : ℝ)^l * (2 : ℝ)^((k : ℝ)*((R : ℝ)-k) - (gaussianPower R : ℝ) -
          (l : ℝ)*((k : ℝ)-t+l))) := by
  have hR := binaryGaussianCoefficient_le_quadratic R k hk
  have ht := binaryGaussianCoefficient_le_quadratic t l hl
  have ht0 : (0 : ℝ) ≤ binaryGaussianCoefficient t l := by
    exact_mod_cast (binaryGaussianCoefficient_pos hl).le
  have hp : (0 : ℝ) ≤ (72 : ℝ)^l / (2 : ℝ)^(k*l) := by positivity
  calc
    _ = (binaryGaussianCoefficient R k : ℝ) * (binaryGaussianCoefficient t l : ℝ) *
        ((72 : ℝ)^l / (2 : ℝ)^(k*l)) := by ring
    _ ≤ (eulerProduct⁻¹ * (2 : ℝ)^(k*(R-k))) *
        (eulerProduct⁻¹ * (2 : ℝ)^(l*(t-l))) *
        ((72 : ℝ)^l / (2 : ℝ)^(k*l)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul hR ht ht0 (by positivity [euler_positive])) hp
    _ = _ := by
      have hpow : (2 : ℝ)^(k*(R-k)) * (2 : ℝ)^(l*(t-l)) / (2 : ℝ)^(k*l) =
          (2 : ℝ)^gaussianPower R *
            (2 : ℝ)^((k : ℝ)*((R : ℝ)-k) - (gaussianPower R : ℝ) -
              (l : ℝ)*((k : ℝ)-t+l)) := by
        simp only [← Real.rpow_natCast]
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
          ← Real.rpow_sub (by norm_num : (0 : ℝ) < 2),
          ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        congr 1
        push_cast [Nat.cast_sub hk,Nat.cast_sub hl]
        ring
      calc
        _ = (eulerProduct⁻¹)^2 * (72 : ℝ)^l *
            ((2 : ℝ)^(k*(R-k)) * (2 : ℝ)^(l*(t-l)) / (2 : ℝ)^(k*l)) := by ring
        _ = _ := by rw [hpow]; ring

/-- The complete exceptional sum has a uniform exponential deficit relative
to the exact Gaussian count. No asymptotic range or parity restriction is
needed; the gap may be zero. -/
theorem exceptionalGaussianSum_le (R t : ℕ) (hd : 0 ≤ (R : ℝ)/2-t) :
    exceptionalGaussianSum R t ≤ exceptionalGaussianConstant * (binaryGaussianSum R : ℝ) *
      (2 : ℝ)^(-((R : ℝ)/2-t)) := by
  let A : ℝ := (eulerProduct⁻¹)^2 * (2 : ℝ)^gaussianPower R
  let C : ℝ := (2 : ℝ)^(66 : ℕ) * halfLatticeGaussianSum
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity [halfLatticeGaussianSum_pos]
  have hpow : (2 : ℝ)^gaussianPower R ≤ (binaryGaussianSum R : ℝ) / eulerProduct := by
    apply (le_div_iff₀ euler_positive).mpr
    simpa only [mul_comm] using quadratic_le_binaryGaussianSum R
  unfold exceptionalGaussianSum
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ l ∈ Finset.Icc 1 t, ∑ k ∈ Finset.range (R+1), A *
        ((72 : ℝ)^l * (2 : ℝ)^((k : ℝ)*((R : ℝ)-k) - (gaussianPower R : ℝ) -
          (l : ℝ)*((k : ℝ)-t+l))) := by
      apply Finset.sum_le_sum
      intro l hl
      apply Finset.sum_le_sum
      intro k hk
      exact exceptionalGaussian_term_le R t k l (by simpa using hk) (Finset.mem_Icc.mp hl).2
    _ = A * (∑ l ∈ Finset.Icc 1 t, ∑ k ∈ Finset.range (R+1),
        (72 : ℝ)^l * (2 : ℝ)^((k : ℝ)*((R : ℝ)-k) - (gaussianPower R : ℝ) -
          (l : ℝ)*((k : ℝ)-t+l))) := by simp_rw [Finset.mul_sum]
    _ ≤ A * (C * (2 : ℝ)^(-((R : ℝ)/2-t))) :=
      mul_le_mul_of_nonneg_left (exceptionalIncidence_kernel_sum_le R t hd) hA
    _ = ((eulerProduct⁻¹)^2 * C * (2 : ℝ)^(-((R : ℝ)/2-t))) *
        (2 : ℝ)^gaussianPower R := by dsimp [A]; ring
    _ ≤ ((eulerProduct⁻¹)^2 * C * (2 : ℝ)^(-((R : ℝ)/2-t))) *
        ((binaryGaussianSum R : ℝ) / eulerProduct) :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = _ := by
      dsimp [C,exceptionalGaussianConstant]
      field_simp

/-- The relative exceptional incidence bound uses the literal Gaussian sum
appearing in the approved benchmark. -/
theorem exceptionalGaussianSum_div_le (R t : ℕ) (hd : 0 ≤ (R : ℝ)/2-t) :
    exceptionalGaussianSum R t / (binaryGaussianSum R : ℝ) ≤
      exceptionalGaussianConstant * (2 : ℝ)^(-((R : ℝ)/2-t)) := by
  apply (div_le_iff₀ (by exact_mod_cast binaryGaussianSum_pos R)).mpr
  simpa only [mul_assoc,mul_comm,mul_left_comm] using exceptionalGaussianSum_le R t hd

/-- A single constant works for every profile whose retained dimension gap
is at least the chosen nonnegative threshold. -/
theorem exceptionalGaussianSum_le_of_gap (R t : ℕ) (d : ℝ)
    (hd : 0 ≤ d) (hgap : d ≤ (R : ℝ)/2-t) :
    exceptionalGaussianSum R t ≤ exceptionalGaussianConstant * (binaryGaussianSum R : ℝ) *
      (2 : ℝ)^(-d) := by
  calc
    _ ≤ exceptionalGaussianConstant * (binaryGaussianSum R : ℝ) *
        (2 : ℝ)^(-((R : ℝ)/2-t)) := exceptionalGaussianSum_le R t (hd.trans hgap)
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) (neg_le_neg hgap))
      (mul_nonneg exceptionalGaussianConstant_pos.le
        (by exact_mod_cast (binaryGaussianSum_pos R).le))

end SymmetricSubgroupAsymptotics
