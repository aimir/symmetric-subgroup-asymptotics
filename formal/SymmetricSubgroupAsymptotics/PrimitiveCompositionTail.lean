import SymmetricSubgroupAsymptotics.PrimitiveCompositionLengthInput
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! The entire primitive composition-weight tail. Exact integer powers
settle degrees45–63; a dyadic induction settles every larger degree.
There is no numerical approximation of logarithms. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics

private theorem primitive_composition_dyadic (k : ℕ) :
    80*(k+6)+40<9*2^(k+6) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [show k.succ+6=(k+6)+1 by omega,pow_succ]
    nlinarith

set_option maxRecDepth 8192 in
private theorem primitive_composition_finite :
    ∀r:Fin 64,45≤r.val → r.val^80<2^(9*r.val+40) := by decide +kernel

theorem primitive_composition_log_tail (r : ℕ) (hr : 45≤r) :
    (8/3:ℝ)*Real.logb 2 r-4/3 < (3/10:ℝ)*r := by
  have hr0 : r≠0 := by omega
  have hrpos : (0:ℝ)<r := by exact_mod_cast (show 0<r by omega)
  by_cases hr64 : r<64
  · have hn := primitive_composition_finite ⟨r,hr64⟩ hr
    have hp : (r:ℝ)^80<(2:ℝ)^(9*r+40) := by exact_mod_cast hn
    have hl := Real.logb_lt_logb (by norm_num : (1:ℝ)<2) (pow_pos hrpos 80) hp
    simp only [Real.logb_pow,Real.logb_self_eq_one (by norm_num : (1:ℝ)<2),
      mul_one,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] at hl
    linarith
  · let k := Nat.log 2 r
    have hk : 6≤k :=
      (Nat.le_log_iff_pow_le (by decide : 1<2) hr0).mpr (by norm_num;omega)
    obtain ⟨j,hj⟩ := Nat.exists_eq_add_of_le hk
    have hd : 80*k+40<9*2^k := by
      rw [hj,Nat.add_comm 6 j]
      exact primitive_composition_dyadic j
    have hlo : 2^k≤r := Nat.pow_log_le_self 2 hr0
    have hhi : r<2^(k+1) := Nat.lt_pow_succ_log_self (by decide : 1<2) r
    have hp : (r:ℝ)<(2:ℝ)^(k+1) := by exact_mod_cast hhi
    have hl := Real.logb_lt_logb (by norm_num : (1:ℝ)<2) hrpos hp
    simp only [Real.logb_pow,Real.logb_self_eq_one (by norm_num : (1:ℝ)<2),
      mul_one,Nat.cast_add,Nat.cast_one] at hl
    have hnum : (80:ℝ)*k+40<9*r := by exact_mod_cast hd.trans_le (Nat.mul_le_mul_left 9 hlo)
    linarith

/-- Every chosen actual chief series in a primitive degree≥45 action
has the strict density needed by the imprimitive c=1 induction. -/
theorem primitiveChiefWeight_strict_tail (hcomp : PrimitiveCompositionLengthInput)
    (r : ℕ) (hr : 45≤r) (U : Subgroup (Equiv.Perm (Fin r)))
    (hprim : MulAction.IsPreprimitive U (Fin r)) (s : ActualChiefSeries U) :
    10*actualChiefSeriesTernaryWeight s<3*r := by
  have h := (primitiveChiefWeight_le_log hcomp r (by omega) U hprim s).trans_lt
    (primitive_composition_log_tail r hr)
  have h' : (10:ℝ)*actualChiefSeriesTernaryWeight s<3*r := by linarith
  exact_mod_cast h'

end SymmetricSubgroupAsymptotics
