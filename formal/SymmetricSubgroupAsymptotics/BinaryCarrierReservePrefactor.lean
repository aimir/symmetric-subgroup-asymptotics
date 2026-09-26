import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-! A finite, uniform logarithmic envelope for the carrier reserve's
actual prefactors. The structured constant M is a symbolic parameter:
neither it nor the source-order constant q is evaluated. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics.BinaryCarrierReservePrefactor

def value (b M q R c L : ℕ) (A : ℝ) : ℝ :=
  ((M : ℝ) * ((b : ℝ)*L+2)^M)^L * A * (R+1) *
    (∑ ell ∈ Finset.range (c+1), (72 : ℝ)^ell) * (2 : ℝ)^(q*L)

private def majorant (b M q R c L : ℕ) (A : ℝ) : ℝ :=
  ((M : ℝ) * ((b : ℝ)*L+2)^M)^L * A * (R+1) *
    (c+1) * (72 : ℝ)^c * (2 : ℝ)^(q*L)

/-- An explicit constant, deliberately coarse and independent of all
profile lengths and dimensions. -/
def logConstant (b M q : ℕ) (A : ℝ) : ℝ :=
  ((M : ℝ)+M*(b+2)+|Real.log A|+72+2*q) / Real.log 2 + M+2

theorem logConstant_nonneg (b M q : ℕ) (A : ℝ) : 0 ≤ logConstant b M q A := by
  unfold logConstant
  positivity [Real.log_pos (by norm_num : (1 : ℝ) < 2)]

theorem relation_sum_le (c : ℕ) :
    (∑ ell ∈ Finset.range (c+1), (72 : ℝ)^ell) ≤ (c+1)*(72 : ℝ)^c := by
  calc
    _ ≤ ∑ _ell ∈ Finset.range (c+1), (72 : ℝ)^c := by
      apply Finset.sum_le_sum
      intro ell hell
      exact pow_le_pow_right₀ (by norm_num) (by simpa using hell)
    _ = _ := by simp

private theorem value_le_majorant (b M q R c L : ℕ) (A : ℝ) (hA : 0 ≤ A) :
    value b M q R c L A ≤ majorant b M q R c L A := by
  unfold value majorant
  calc
    _ ≤ ((M : ℝ)*((b : ℝ)*L+2)^M)^L * A * (R+1) *
        ((c+1)*(72 : ℝ)^c) * (2 : ℝ)^(q*L) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left (relation_sum_le c) (by positivity)
    _ = _ := by ring

private theorem log_majorant (b M q R c L : ℕ) (A : ℝ)
    (hM : 0 < M) (hA : 0 < A) :
    Real.log (majorant b M q R c L A) =
      (L : ℝ)*(Real.log M+M*Real.log ((b : ℝ)*L+2)) + Real.log A +
        Real.log (R+1) + Real.log (c+1) + c*Real.log 72 +
          q*L*Real.log 2 := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hb : (0 : ℝ) < (b : ℝ)*L+2 := by positivity
  have hR : (0 : ℝ) < (R : ℝ)+1 := by positivity
  have hc : (0 : ℝ) < (c : ℝ)+1 := by positivity
  simp [majorant, Real.log_mul, Real.log_pow, hMr.ne', hb.ne', hA.ne', hR.ne', hc.ne']
  <;> ring

private theorem log_majorant_le (b M q R c L : ℕ) (A N : ℝ)
    (hM : 0 < M) (hA : 0 < A) (hN : 1 ≤ N)
    (hR : (R : ℝ) ≤ N) (hc : (c : ℝ) ≤ N) (hL : (L : ℝ) ≤ N) :
    Real.log (majorant b M q R c L A) ≤
      logConstant b M q A * N * Real.log (N+2) := by
  have hN0 : 0 ≤ N := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : Real.log 2 ≤ Real.log (N+2) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hlog0 : 0 ≤ Real.log (N+2) := hlog2.le.trans hlog
  have hscale (x : ℝ) (hx : 0 ≤ x) :
      x*N ≤ (x/Real.log 2)*(N*Real.log (N+2)) := by
    calc
      _ = (x/Real.log 2)*(N*Real.log 2) := by field_simp [hlog2.ne'] <;> ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hlog hN0) (div_nonneg hx hlog2.le)
  have hlog_le : Real.log (N+2) ≤ N*Real.log (N+2) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hN) hlog0]
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have hbase : (0 : ℝ) < (b : ℝ)*L+2 := by positivity
  have hbase_le : (b : ℝ)*L+2 ≤ ((b : ℝ)+2)*(N+2) := by
    nlinarith [mul_nonneg (Nat.cast_nonneg b) (sub_nonneg.mpr hL)]
  have hlogbase : Real.log ((b : ℝ)*L+2) ≤ (b : ℝ)+2+Real.log (N+2) := by
    have h := Real.log_le_log hbase hbase_le
    rw [Real.log_mul (by positivity : (b : ℝ)+2 ≠ 0)
      (by positivity : N+2 ≠ 0)] at h
    have hb := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < (b : ℝ)+2)
    linarith
  have hlogM : Real.log (M : ℝ) ≤ M :=
    (Real.log_le_sub_one_of_pos hMr).trans (by linarith)
  have hstructured :
      (L : ℝ)*(Real.log M+M*Real.log ((b : ℝ)*L+2)) ≤
        (((M : ℝ)+M*(b+2))/Real.log 2+M)*(N*Real.log (N+2)) := by
    calc
      _ ≤ (L : ℝ)*((M : ℝ)+M*((b : ℝ)+2+Real.log (N+2))) :=
        mul_le_mul_of_nonneg_left
          (add_le_add hlogM (mul_le_mul_of_nonneg_left hlogbase hMr.le))
          (Nat.cast_nonneg L)
      _ ≤ N*((M : ℝ)+M*((b : ℝ)+2+Real.log (N+2))) :=
        mul_le_mul_of_nonneg_right hL (by positivity)
      _ = ((M : ℝ)+M*(b+2))*N+M*(N*Real.log (N+2)) := by ring
      _ ≤ (((M : ℝ)+M*(b+2))/Real.log 2)*(N*Real.log (N+2))+
          M*(N*Real.log (N+2)) :=
        add_le_add (hscale ((M : ℝ)+M*(b+2)) (by positivity)) le_rfl
      _ = _ := by ring
  have hconstant : Real.log A ≤
      (|Real.log A|/Real.log 2)*(N*Real.log (N+2)) := by
    calc
      _ ≤ |Real.log A| := le_abs_self _
      _ ≤ |Real.log A| * N := by nlinarith [abs_nonneg (Real.log A)]
      _ ≤ _ := hscale _ (abs_nonneg _)
  have hRlog : Real.log ((R : ℝ)+1) ≤ N*Real.log (N+2) :=
    (Real.log_le_log (by positivity) (by linarith)).trans hlog_le
  have hclog : Real.log ((c : ℝ)+1) ≤ N*Real.log (N+2) :=
    (Real.log_le_log (by positivity) (by linarith)).trans hlog_le
  have h72 : (c : ℝ)*Real.log 72 ≤ (72/Real.log 2)*(N*Real.log (N+2)) := by
    have he : Real.log (72 : ℝ) ≤ 72 :=
      (Real.log_le_sub_one_of_pos (by norm_num)).trans (by norm_num)
    calc
      _ ≤ (c : ℝ)*72 := mul_le_mul_of_nonneg_left he (Nat.cast_nonneg c)
      _ ≤ 72*N := by linarith
      _ ≤ _ := hscale 72 (by norm_num)
  have hq : (q : ℝ)*L*Real.log 2 ≤
      (2*q/Real.log 2)*(N*Real.log (N+2)) := by
    have he : Real.log (2 : ℝ) ≤ 2 :=
      (Real.log_le_sub_one_of_pos (by norm_num)).trans (by norm_num)
    calc
      _ ≤ ((q : ℝ)*N)*2 := mul_le_mul
        (mul_le_mul_of_nonneg_left hL (Nat.cast_nonneg q)) he hlog2.le (by positivity)
      _ = (2*q)*N := by ring
      _ ≤ _ := hscale _ (by positivity)
  rw [log_majorant b M q R c L A hM hA]
  calc
    _ ≤ ((((M : ℝ)+M*(b+2))/Real.log 2+M) +
        |Real.log A|/Real.log 2+1+1+72/Real.log 2+2*q/Real.log 2) *
          (N*Real.log (N+2)) := by
      linarith only [hstructured, hconstant, hRlog, hclog, h72, hq]
    _ = _ := by unfold logConstant; ring

/-- The finite prefactor is bounded at every N≥1, with no limiting or
counting assumption and with the whole original relation sum included. -/
theorem value_le (b M q R c L : ℕ) (A N : ℝ)
    (hM : 0 < M) (hA : 0 < A) (hN : 1 ≤ N)
    (hR : (R : ℝ) ≤ N) (hc : (c : ℝ) ≤ N) (hL : (L : ℝ) ≤ N) :
    value b M q R c L A ≤
      (2 : ℝ)^((logConstant b M q A/Real.log 2)*N*Real.log (N+2)) := by
  have hpos : 0 < majorant b M q R c L A := by
    have hMr : (0 : ℝ) < M := by exact_mod_cast hM
    unfold majorant
    positivity
  apply (value_le_majorant b M q R c L A hA.le).trans
  have h := (Real.log_le_iff_le_exp hpos).mp
    (log_majorant_le b M q R c L A N hM hA hN hR hc hL)
  convert h using 1
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  congr 1
  have hlog2 : Real.log (2 : ℝ) ≠ 0 := (Real.log_pos (by norm_num)).ne'
  field_simp [hlog2] <;> ring

end SymmetricSubgroupAsymptotics.BinaryCarrierReservePrefactor
