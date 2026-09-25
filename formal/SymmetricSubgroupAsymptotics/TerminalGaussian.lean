import SymmetricSubgroupAsymptotics.ExceptionalGaussianBound

/-!
# The complete terminal Gaussian double sum

These are unconditional estimates for explicit finite sums. No subgroup
incidence inequality or cohomological realization statement is assumed here.
The exterior character rank is arbitrary, including the endpoint regime
where it is at least the critical quotient rank.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics

/-- The literal Gaussian attachment weight of an exterior of character rank `d`. -/
def terminalGaussianWeight (r d : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (r + 1), (binaryGaussianCoefficient r j : ℝ) * (2 : ℝ)^(d*j)

/-- The complete positive double sum in the terminal estimate, including its
two original Euler-product factors. -/
def terminalGaussianDoubleSum (r c d τ : ℕ) : ℝ :=
  (eulerProduct⁻¹)^2 * ∑ j ∈ Finset.range (r + 1), ∑ l ∈ Finset.range (c + 1),
    (binaryGaussianCoefficient c l : ℝ) * (72 : ℝ)^l *
      (2 : ℝ)^((τ : ℝ)*l + ((j : ℝ)-l)*((r : ℝ)-j+d))

/-- The sharp elementary lower bound on each Gaussian coefficient. -/
theorem terminal_gaussianCoefficient_lower (r k : ℕ) (hk : k ≤ r) :
    (2 : ℝ)^(k*(r-k)) ≤ (binaryGaussianCoefficient r k : ℝ) := by
  have hq : (2 : ℚ)^(k*(r-k)) ≤ binaryGaussianCoefficient r k := by
    unfold binaryGaussianCoefficient
    calc
      _ = ∏ _i ∈ Finset.range k, (2 : ℚ)^(r-k) := by
        simp [← pow_mul, Nat.mul_comm]
      _ ≤ _ := by
        apply Finset.prod_le_prod
        · intro i hi
          positivity
        · intro i hi
          have hik : i < k := Finset.mem_range.mp hi
          apply (le_div_iff₀ (binaryGaussian_denominator_pos hik)).mpr
          have he : (2 : ℚ)^(r-k) * 2^k = 2^r := by
            rw [← pow_add, Nat.sub_add_cancel hk]
          have hp : (1 : ℚ) ≤ 2^(r-k) := one_le_pow₀ (by norm_num)
          have hi0 : (0 : ℚ) ≤ 2^i := by positivity
          nlinarith
  exact_mod_cast hq

theorem terminalGaussianWeight_term_le (r d j : ℕ) (hj : j ≤ r) :
    (2 : ℝ)^((j : ℝ)*((r : ℝ)-j+d)) ≤ terminalGaussianWeight r d := by
  calc
    _ = (2 : ℝ)^(j*(r-j)) * (2 : ℝ)^(d*j) := by
      simp only [← Real.rpow_natCast]
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      push_cast [Nat.cast_sub hj]
      ring
    _ ≤ (binaryGaussianCoefficient r j : ℝ) * (2 : ℝ)^(d*j) :=
      mul_le_mul_of_nonneg_right (terminal_gaussianCoefficient_lower r j hj) (by positivity)
    _ ≤ _ := by
      unfold terminalGaussianWeight
      apply Finset.single_le_sum (s := Finset.range (r+1))
        (f := fun k => (binaryGaussianCoefficient r k : ℝ) * (2 : ℝ)^(d*k)) (a := j)
      · intro k hk
        exact mul_nonneg (by exact_mod_cast (binaryGaussianCoefficient_pos
          (r := r) (k := k) (by simpa using hk)).le) (by positivity)
      · exact Finset.mem_range.mpr (by omega)

theorem terminalGaussianWeight_pos (r d : ℕ) : 0 < terminalGaussianWeight r d := by
  have h := terminalGaussianWeight_term_le r d 0 (Nat.zero_le r)
  norm_num at h
  linarith

/-- A central integer dimension supplies the denominator in the interior
regime. The exact parity loss is still present in `gaussianPower`. -/
theorem terminalGaussianWeight_central_lower (r d : ℕ) (hd : d ≤ r) :
    (2 : ℝ)^gaussianPower (r+d) ≤ terminalGaussianWeight r d := by
  have hj : (r+d)/2 ≤ r := by omega
  have h := terminalGaussianWeight_term_le r d ((r+d)/2) hj
  convert h using 1
  rw [← Real.rpow_natCast]
  congr 1
  unfold gaussianPower
  push_cast [Nat.cast_sub (Nat.div_le_self (r+d) 2)]
  ring

/-- The actual last term supplies the denominator in the exterior-dominated
regime; in fact this lower bound holds for every exterior rank. -/
theorem terminalGaussianWeight_endpoint_lower (r d : ℕ) :
    (2 : ℝ)^((r : ℝ)*d) ≤ terminalGaussianWeight r d := by
  simpa using terminalGaussianWeight_term_le r d r le_rfl

/-- The residual relation weight in the uniform ratio. Keeping `72^l`
separate is exactly equivalent to the `log₂ 72` form. -/
def terminalRelationWeight (r c d τ l : ℕ) : ℝ :=
  (72 : ℝ)^l * (2 : ℝ)^(-((l : ℝ)*((r : ℝ)/2-c+d/2-τ)) - 3*(l : ℝ)^2/4)

/-- The endpoint retains the additional negative exterior-rank and relation
dimension corrections rather than extending an interior maximum. -/
def terminalEndpointRelationWeight (c d τ l : ℕ) : ℝ :=
  (72 : ℝ)^l * (2 : ℝ)^((l : ℝ)*((c : ℝ)+τ-d-l))

theorem terminal_exponent_interior (r c d τ j l : ℕ) :
    (l : ℝ)*((c : ℝ)-l) + (τ : ℝ)*l +
        ((j : ℝ)-l)*((r : ℝ)-j+d) - (gaussianPower (r+d) : ℝ) =
      ((r+d)%2 : ℕ)/4 - ((j : ℝ)-((r : ℝ)+d+l)/2)^2 -
        (l : ℝ)*((r : ℝ)/2-c+d/2-τ) - 3*(l : ℝ)^2/4 := by
  rw [gaussianPower_quadratic]
  push_cast
  ring

theorem terminal_exponent_endpoint (r c d τ j l : ℕ) :
    (l : ℝ)*((c : ℝ)-l) + (τ : ℝ)*l +
        ((j : ℝ)-l)*((r : ℝ)-j+d) - (r : ℝ)*d =
      (l : ℝ)*((c : ℝ)+τ-d-l) - ((r : ℝ)-j)*((d : ℝ)+l-j) := by
  ring

theorem terminalEndpointRelationWeight_le (r c d τ l : ℕ) (hd : r ≤ d) :
    terminalEndpointRelationWeight c d τ l ≤ terminalRelationWeight r c d τ l := by
  unfold terminalEndpointRelationWeight terminalRelationWeight
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have hd' : (r : ℝ) ≤ d := by exact_mod_cast hd
  have hl : (0 : ℝ) ≤ l := by positivity
  nlinarith [mul_nonneg hl (sub_nonneg.mpr hd'), sq_nonneg (l : ℝ)]

private theorem terminal_term_le (r c d τ j l : ℕ) (hl : l ≤ c)
    (b v X : ℝ) (hb : (2 : ℝ)^b ≤ X)
    (hv : (l : ℝ)*((c : ℝ)-l) + (τ : ℝ)*l +
      ((j : ℝ)-l)*((r : ℝ)-j+d) ≤ b+v) :
    (binaryGaussianCoefficient c l : ℝ) * (72 : ℝ)^l *
      (2 : ℝ)^((τ : ℝ)*l + ((j : ℝ)-l)*((r : ℝ)-j+d)) ≤
        eulerProduct⁻¹ * X * ((72 : ℝ)^l * (2 : ℝ)^v) := by
  have hcoeff := binaryGaussianCoefficient_le_quadratic c l hl
  calc
    _ ≤ (eulerProduct⁻¹ * (2 : ℝ)^(l*(c-l))) * (72 : ℝ)^l *
        (2 : ℝ)^((τ : ℝ)*l + ((j : ℝ)-l)*((r : ℝ)-j+d)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcoeff (by positivity)) (by positivity)
    _ = eulerProduct⁻¹ * (72 : ℝ)^l *
        (2 : ℝ)^((l : ℝ)*((c : ℝ)-l) + (τ : ℝ)*l +
          ((j : ℝ)-l)*((r : ℝ)-j+d)) := by
      have hp : (2 : ℝ)^(l*(c-l)) *
          (2 : ℝ)^((τ : ℝ)*l + ((j : ℝ)-l)*((r : ℝ)-j+d)) =
          (2 : ℝ)^((l : ℝ)*((c : ℝ)-l) + (τ : ℝ)*l +
            ((j : ℝ)-l)*((r : ℝ)-j+d)) := by
        rw [← Real.rpow_natCast (2 : ℝ) (l*(c-l)),
          ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        congr 1
        push_cast [Nat.cast_sub hl]
        ring
      calc
        _ = eulerProduct⁻¹ * (72 : ℝ)^l * ((2 : ℝ)^(l*(c-l)) *
          (2 : ℝ)^((τ : ℝ)*l + ((j : ℝ)-l)*((r : ℝ)-j+d))) := by ring
        _ = _ := by rw [hp]
    _ ≤ eulerProduct⁻¹ * (72 : ℝ)^l * (2 : ℝ)^(b+v) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (by norm_num) hv)
        (by positivity [euler_positive])
    _ ≤ eulerProduct⁻¹ * X * ((72 : ℝ)^l * (2 : ℝ)^v) := by
      rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      calc
        _ = (eulerProduct⁻¹ * (72 : ℝ)^l * (2 : ℝ)^v) * (2 : ℝ)^b := by ring
        _ ≤ (eulerProduct⁻¹ * (72 : ℝ)^l * (2 : ℝ)^v) * X :=
          mul_le_mul_of_nonneg_left hb (by positivity [euler_positive])
        _ = _ := by ring

theorem terminalGaussian_term_interior_le (r c d τ j l : ℕ)
    (hd : d ≤ r) (hl : l ≤ c) :
    (binaryGaussianCoefficient c l : ℝ) * (72 : ℝ)^l *
      (2 : ℝ)^((τ : ℝ)*l + ((j : ℝ)-l)*((r : ℝ)-j+d)) ≤
        2 * eulerProduct⁻¹ * terminalGaussianWeight r d * terminalRelationWeight r c d τ l := by
  have hb : (2 : ℝ)^((gaussianPower (r+d) : ℝ)+1) ≤
      2 * terminalGaussianWeight r d := by
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one, Real.rpow_natCast]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left
      (terminalGaussianWeight_central_lower r d hd) (by norm_num : (0 : ℝ) ≤ 2)
  have hp : (((r+d)%2 : ℕ) : ℝ) ≤ 1 := by
    exact_mod_cast (show (r+d)%2 ≤ 1 by omega)
  have he := terminal_exponent_interior r c d τ j l
  have h := terminal_term_le r c d τ j l hl _ _ _ hb
    (show (l : ℝ)*((c : ℝ)-l) + (τ : ℝ)*l +
      ((j : ℝ)-l)*((r : ℝ)-j+d) ≤
      (gaussianPower (r+d) : ℝ)+1 +
        (-((l : ℝ)*((r : ℝ)/2-c+d/2-τ))-3*(l : ℝ)^2/4) by
      nlinarith [sq_nonneg ((j : ℝ)-((r : ℝ)+d+l)/2)])
  simpa only [terminalRelationWeight, mul_assoc, mul_comm, mul_left_comm] using h

theorem terminalGaussian_term_endpoint_le (r c d τ j l : ℕ)
    (hd : r ≤ d) (hj : j ≤ r) (hl : l ≤ c) :
    (binaryGaussianCoefficient c l : ℝ) * (72 : ℝ)^l *
      (2 : ℝ)^((τ : ℝ)*l + ((j : ℝ)-l)*((r : ℝ)-j+d)) ≤
        eulerProduct⁻¹ * terminalGaussianWeight r d * terminalEndpointRelationWeight c d τ l := by
  have hj' : (j : ℝ) ≤ r := by exact_mod_cast hj
  have hd' : (r : ℝ) ≤ d := by exact_mod_cast hd
  have he := terminal_exponent_endpoint r c d τ j l
  apply terminal_term_le r c d τ j l hl _ _ _ (terminalGaussianWeight_endpoint_lower r d)
  have hp : 0 ≤ ((r : ℝ)-j)*((d : ℝ)+l-j) :=
    mul_nonneg (by linarith) (by
      have : (0 : ℝ) ≤ l := by positivity
      linarith)
  linarith

end SymmetricSubgroupAsymptotics
