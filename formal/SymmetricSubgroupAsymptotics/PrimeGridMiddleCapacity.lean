import SymmetricSubgroupAsymptotics.PrimeGridMiddleBound
import SymmetricSubgroupAsymptotics.CentralBinomialSquareRootBound

/-! Real numerical capacities from the proved integer middle counts. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

theorem primeGridMiddleWidth_normalized (p r : ℕ) (hp : 0<p) :
    (primeGridMiddleWidth p r : ℝ)≤(p : ℝ)^r*
      ((r*(p-1)).choose ((r*(p-1))/2) : ℝ)/(2 : ℝ)^(r*(p-1)) := by
  have h : (2 : ℝ)^(r*(p-1))*(primeGridMiddleWidth p r : ℝ)≤
      (p : ℝ)^r*((r*(p-1)).choose ((r*(p-1))/2) : ℝ) := by
    exact_mod_cast primeGridMiddleWidth_binomial p r hp
  apply (le_div_iff₀ (by positivity : (0 : ℝ)<(2 : ℝ)^(r*(p-1)))).mpr
  nlinarith [h]

/-- A common lower exponent bounds every literal Sylow orbit with the
same characteristic-primary square-root coefficient. -/
theorem primeGridMiddleWidth_primary (p r e : ℕ) (hp : 2≤p) (he : 1≤e) (her : e≤r) :
    (primeGridMiddleWidth p r : ℝ)≤(p : ℝ)^r*
      Real.sqrt (2/(3*((p : ℝ)-1)*e)) := by
  have hr : 1≤r := he.trans her
  have hpm : 1≤p-1 := by omega
  have hK : 1≤r*(p-1) := by nlinarith
  have hpe : (0 : ℝ)<(p : ℝ)-1 := by
    have h : (2 : ℝ)≤p := by exact_mod_cast hp
    linarith
  have hepos : (0 : ℝ)<e := by exact_mod_cast he
  have hd : 3*((p : ℝ)-1)*e≤3*((r*(p-1) : ℕ) : ℝ) := by
    have hm : (p-1)*e≤r*(p-1) := by nlinarith
    have hcast : (((p-1)*e : ℕ) : ℝ)≤((r*(p-1) : ℕ) : ℝ) := by exact_mod_cast hm
    rw [Nat.cast_mul,Nat.cast_sub (by omega : 1≤p),Nat.cast_one] at hcast
    nlinarith
  have hs : Real.sqrt (2/(3*((r*(p-1) : ℕ) : ℝ)))≤
      Real.sqrt (2/(3*((p : ℝ)-1)*e)) := by
    apply Real.sqrt_le_sqrt
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hd
  calc
    (primeGridMiddleWidth p r : ℝ)≤(p : ℝ)^r*
        ((r*(p-1)).choose ((r*(p-1))/2) : ℝ)/(2 : ℝ)^(r*(p-1)) :=
      primeGridMiddleWidth_normalized p r (by omega)
    _ = (p : ℝ)^r*
        (((r*(p-1)).choose ((r*(p-1))/2) : ℝ)/(2 : ℝ)^(r*(p-1))) := by ring
    _ ≤ (p : ℝ)^r*Real.sqrt (2/(3*((r*(p-1) : ℕ) : ℝ))) :=
      mul_le_mul_of_nonneg_left
        (CentralBinomialSquareRootBound.normalized_le_sqrt _ hK) (by positivity)
    _ ≤ (p : ℝ)^r*Real.sqrt (2/(3*((p : ℝ)-1)*e)) :=
      mul_le_mul_of_nonneg_left hs (by positivity)

end SymmetricSubgroupAsymptotics
