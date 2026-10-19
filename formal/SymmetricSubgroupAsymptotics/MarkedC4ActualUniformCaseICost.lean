import SymmetricSubgroupAsymptotics.MarkedC4ActualUniversalCaseINormalized
import SymmetricSubgroupAsymptotics.MarkedC4ActualHallColumnCompression
import Mathlib.Data.Nat.Factorial.Basic

/-! Uniform physical cost for Case I. The actual abelian order supplies
all column bounds; the global marking polynomial is absent from this cost. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualUniformCaseICost
open ActualSingleGlobalHallPolynomial ActualUniversalCaseINormalized

theorem physical_polynomial_le (m b : ℕ) (A : Type) [CommGroup A] [Finite A]
    (hA : HasExp2 A (2+m))
    (hcard : (Nat.card A : ℝ)≤(2 : ℝ)^((b : ℝ)/2)) :
    physicalPolynomial m A≤((b : ℝ)+2)^(3*m+2) := by
  have hm := ActualHallColumnCompression.column_mass_le (2+m) A hA hcard
  have hcol (k : ℕ) (hk : k∈Finset.range (2+m)) :
      (col A k : ℝ)+1≤(b : ℝ)+2 := by
    have hk' : (col A k : ℝ)≤∑ j∈Finset.range (2+m),(col A j : ℝ) :=
      Finset.single_le_sum (fun _ _ => Nat.cast_nonneg _) hk
    have hb : (0 : ℝ)≤b := Nat.cast_nonneg _
    linarith
  have hp : (∏ k∈Finset.range (2+m),((col A k : ℝ)+1))≤
      ((b : ℝ)+2)^(2+m) := by
    calc
      _≤∏ _k∈Finset.range (2+m),((b : ℝ)+2) := by
        apply Finset.prod_le_prod
        · intro k hk
          positivity
        · exact hcol
      _=_ := by simp
  have hfour : (4 : ℝ)^m≤((b : ℝ)+2)^(2*m) := by
    have hb : (4 : ℝ)≤((b : ℝ)+2)^2 := by
      have : (0 : ℝ)≤b := Nat.cast_nonneg _
      nlinarith
    simpa only [pow_mul] using pow_le_pow_left₀ (by norm_num : (0 : ℝ)≤4) hb m
  unfold physicalPolynomial
  calc
    _≤((b : ℝ)+2)^(2*m)*((b : ℝ)+2)^(2+m) :=
      mul_le_mul hfour hp (by positivity) (by positivity)
    _=_ := by rw [← pow_add]; congr 1; omega

theorem physical_cost_le (t K m b : ℕ) (ht : t≤b)
    (A : Type) [CommGroup A] [Finite A] (hA : HasExp2 A (2+m))
    (hcard : (Nat.card A : ℝ)≤(2 : ℝ)^((b : ℝ)/2)) (B : ℝ) :
    physicalCost t K m A B≤((b : ℝ)+2)^
      ((((1+2^K)*b+3*m+2 : ℕ) : ℝ)+(b : ℝ)*B^2) := by
  have hb0 : (0 : ℝ)<(b : ℝ)+2 := by positivity
  have hb : (0 : ℝ)≤b := Nat.cast_nonneg _
  have hb1 : (1 : ℝ)≤(b : ℝ)+2 := by linarith
  have hfac : t.factorial≤(b+2)^t :=
    t.factorial_le_pow.trans (pow_le_pow_left₀ (by omega : 0≤t) (by omega : t≤b+2) t)
  have hmenu : t.factorial*(t+1)^((2^K)*t)≤(b+2)^((1+2^K)*b) := by
    calc
      _≤(b+2)^t*(b+2)^((2^K)*t) :=
        Nat.mul_le_mul hfac (pow_le_pow_left₀ (by omega : 0≤t+1) (by omega : t+1≤b+2) _)
      _=(b+2)^((1+2^K)*t) := by rw [← pow_add]; congr 1; ring
      _≤_ := pow_le_pow_right₀ (by omega : 1≤b+2) (Nat.mul_le_mul_left _ ht)
  have hmenu' : ((t.factorial*(t+1)^((2^K)*t) : ℕ) : ℝ)≤
      ((b : ℝ)+2)^((1+2^K)*b) := by exact_mod_cast hmenu
  have hexp : (2 : ℝ)^((t : ℝ)*B^2)≤((b : ℝ)+2)^((b : ℝ)*B^2) := by
    calc
      _≤((b : ℝ)+2)^((t : ℝ)*B^2) :=
        Real.rpow_le_rpow (by norm_num) (by linarith) (by positivity)
      _≤_ := Real.rpow_le_rpow_of_exponent_le hb1
        (mul_le_mul_of_nonneg_right (by exact_mod_cast ht) (sq_nonneg B))
  have hp := physical_polynomial_le m b A hA hcard
  have hp0 : (0 : ℝ)≤physicalPolynomial m A := by
    unfold physicalPolynomial
    apply mul_nonneg (by positivity)
    exact Finset.prod_nonneg (fun _ _ => by positivity)
  unfold physicalCost
  calc
    _≤(((b : ℝ)+2)^((1+2^K)*b)*((b : ℝ)+2)^(3*m+2))*
        ((b : ℝ)+2)^((b : ℝ)*B^2) :=
      mul_le_mul (mul_le_mul hmenu' hp hp0 (by positivity)) hexp
        (by positivity) (by positivity)
    _=_ := by
      rw [← pow_add,← Real.rpow_natCast,← Real.rpow_add hb0]
      congr 1

end SymmetricSubgroupAsymptotics.MarkedC4.ActualUniformCaseICost
