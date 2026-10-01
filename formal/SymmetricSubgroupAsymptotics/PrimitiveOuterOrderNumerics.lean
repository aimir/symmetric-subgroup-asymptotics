import SymmetricSubgroupAsymptotics.PrimitiveSemisimpleCompressionProfile
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Exact numerics for the primitive outer-order bound

The published simple-group input gives `q ≤ 3 log₂ ell`.  Exact integer
power comparisons turn this into the two inequalities consumed by primitive
compression:

* `4q ≤ ell²` for every `ell ≥ 5`;
* `2q ≤ ell` for every `ell ≥ 30`.

The proof uses no floating-point approximation.  Small intervals are checked
by kernel reduction; the tails use elementary dyadic induction.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

private theorem three_logb_lt_of_cube_lt_two_pow
    {ell m : ℕ} (hell : 0 < ell) (hpow : ell ^ 3 < 2 ^ m) :
    3 * Real.logb 2 ell < m := by
  have hp : ((ell : ℝ) ^ 3) < (2 : ℝ) ^ m := by exact_mod_cast hpow
  have hl := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2)
    (pow_pos (by exact_mod_cast hell) 3) hp
  simp only [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),
    mul_one] at hl
  exact_mod_cast hl

private theorem nat_lt_two_pow_sub_two (ell : ℕ) (hell : 10 ≤ ell) :
    ell < 2 ^ (ell - 2) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hell
  induction k with
  | zero => norm_num
  | succ k ih =>
      have hsmall : 10 + Nat.succ k ≤ 2 * (10 + k) := by omega
      have hdouble : 2 * (10 + k) < 2 * 2 ^ (10 + k - 2) :=
        (Nat.mul_lt_mul_left (by omega : 0 < 2)).2 (ih (by omega))
      calc
        10 + Nat.succ k ≤ 2 * (10 + k) := hsmall
        _ < 2 * 2 ^ (10 + k - 2) := hdouble
        _ = 2 ^ (10 + Nat.succ k - 2) := by
          rw [show 10 + Nat.succ k - 2 = (10 + k - 2) + 1 by omega,
            pow_succ]
          ring

private theorem primitive_outer_square_small
    (ell q : ℕ) (hell5 : 5 ≤ ell) (hell10 : ell < 10)
    (hout : (q : ℝ) ≤ 3 * Real.logb 2 ell) :
    4 * q ≤ ell ^ 2 := by
  interval_cases ell <;>
    first
    | have hlog := three_logb_lt_of_cube_lt_two_pow
        (ell := 5) (m := 7) (by norm_num) (by norm_num)
      have hq : q < 7 := by exact_mod_cast hout.trans_lt hlog
      omega
    | have hlog := three_logb_lt_of_cube_lt_two_pow
        (ell := 6) (m := 8) (by norm_num) (by norm_num)
      have hq : q < 8 := by exact_mod_cast hout.trans_lt hlog
      omega
    | have hlog := three_logb_lt_of_cube_lt_two_pow
        (ell := 7) (m := 9) (by norm_num) (by norm_num)
      have hq : q < 9 := by exact_mod_cast hout.trans_lt hlog
      omega
    | have hlog := three_logb_lt_of_cube_lt_two_pow
        (ell := 8) (m := 10) (by norm_num) (by norm_num)
      have hq : q < 10 := by exact_mod_cast hout.trans_lt hlog
      omega
    | have hlog := three_logb_lt_of_cube_lt_two_pow
        (ell := 9) (m := 10) (by norm_num) (by norm_num)
      have hq : q < 10 := by exact_mod_cast hout.trans_lt hlog
      omega

/-- The published logarithmic outer-order estimate implies the exact
two-factor inequality needed for every multi-factor primitive socle. -/
theorem primitive_outerOrder_square_bound
    (ell q : ℕ) (hell : 5 ≤ ell)
    (hout : (q : ℝ) ≤ 3 * Real.logb 2 ell) :
    4 * q ≤ ell ^ 2 := by
  by_cases hsmall : ell < 10
  · exact primitive_outer_square_small ell q hell hsmall hout
  · have hell10 : 10 ≤ ell := by omega
    have hpNat := nat_lt_two_pow_sub_two ell hell10
    have hp : (ell : ℝ) < (2 : ℝ) ^ (ell - 2) := by exact_mod_cast hpNat
    have hlog := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2)
      (by exact_mod_cast (show 0 < ell by omega)) hp
    simp only [Real.logb_pow,
      Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] at hlog
    rw [Nat.cast_sub (by omega : 2 ≤ ell)] at hlog
    have hell10Real : (10 : ℝ) ≤ ell := by exact_mod_cast hell10
    have hquad : (12 : ℝ) * ((ell : ℝ) - 2) ≤ (ell : ℝ) ^ 2 := by
      nlinarith [sq_nonneg ((ell : ℝ) - 10)]
    have hreal : (4 : ℝ) * q < (ell : ℝ) ^ 2 := by
      have hqlog : (4 : ℝ) * q ≤ 12 * Real.logb 2 ell := by nlinarith
      have hlog' : 12 * Real.logb 2 ell < 12 * ((ell : ℝ) - 2) :=
        mul_lt_mul_of_pos_left hlog (by norm_num)
      have : (4 : ℝ) * q < 12 * ((ell : ℝ) - 2) := hqlog.trans_lt hlog'
      exact this.trans_le hquad
    have hnat : 4 * q < ell ^ 2 := by exact_mod_cast hreal
    exact Nat.le_of_lt hnat

private theorem primitive_outer_large_finite :
    ∀ ell : Fin 64, 30 ≤ ell.val →
      ell.val ^ 3 < 2 ^ (ell.val / 2 + 1) := by decide +kernel

private theorem six_succ_le_two_pow (k : ℕ) (hk : 6 ≤ k) :
    6 * (k + 1) ≤ 2 ^ k := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  induction j with
  | zero => norm_num
  | succ j ih =>
      calc
        6 * (6 + Nat.succ j + 1) ≤ 2 * (6 * (6 + j + 1)) := by omega
        _ ≤ 2 * 2 ^ (6 + j) := Nat.mul_le_mul_left 2 (ih (by omega))
        _ = 2 ^ (6 + Nat.succ j) := by
          rw [show 6 + Nat.succ j = (6 + j) + 1 by omega, pow_succ]
          ring

/-- In the almost-simple tail, the same published logarithmic estimate gives
the faithful regular quotient degree at most half the primitive degree. -/
theorem primitive_outerOrder_large_simple_bound
    (ell q : ℕ) (hell : 30 ≤ ell)
    (hout : (q : ℝ) ≤ 3 * Real.logb 2 ell) :
    2 * q ≤ ell := by
  by_cases h64 : ell < 64
  · have hpNat := primitive_outer_large_finite ⟨ell, h64⟩ hell
    have hlog := three_logb_lt_of_cube_lt_two_pow
      (ell := ell) (m := ell / 2 + 1) (by omega) hpNat
    have hqReal : (q : ℝ) < ((ell / 2 + 1 : ℕ) : ℝ) := hout.trans_lt hlog
    have hqNat : q < ell / 2 + 1 := by exact_mod_cast hqReal
    have hq : q ≤ ell / 2 := by omega
    omega
  · let k := Nat.log 2 ell
    have hell0 : ell ≠ 0 := by omega
    have hk : 6 ≤ k :=
      (Nat.le_log_iff_pow_le (by decide : 1 < 2) hell0).mpr (by norm_num; omega)
    have hlo : 2 ^ k ≤ ell := Nat.pow_log_le_self 2 hell0
    have hhi : ell < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by decide : 1 < 2) ell
    have hp : (ell : ℝ) < (2 : ℝ) ^ (k + 1) := by exact_mod_cast hhi
    have hlog := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2)
      (by exact_mod_cast (show 0 < ell by omega)) hp
    simp only [Real.logb_pow,
      Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] at hlog
    have hqReal : (2 : ℝ) * q < (6 : ℝ) * ((k + 1 : ℕ) : ℝ) := by
      nlinarith
    have hqNat : 2 * q < 6 * (k + 1) := by exact_mod_cast hqReal
    exact (Nat.le_of_lt hqNat).trans ((six_succ_le_two_pow k hk).trans hlo)

/-- The primitive-socle data in its natural literature form.  In contrast to
`PrimitiveSemisimpleCompressionProfile`, this structure retains the single
published outer-order estimate instead of asking callers to pre-prove its two
numerical consequences. -/
structure PrimitiveSemisimpleOuterLogProfile
    (L : Type) [Group L] (r : ℕ) where
  E : Subgroup L
  [E_normal : E.Normal]
  chart : SemisimpleNormalChart E
  factorCount : ℕ
  factorCount_pos : 0 < factorCount
  leastIndex : ℕ
  leastIndex_five_le : 5 ≤ leastIndex
  outerOrder : ℕ
  outerOrder_pos : 0 < outerOrder
  quotientAction :
    (L ⧸ E) →* Equiv.Perm (Fin (factorCount * outerOrder))
  quotientAction_injective : Function.Injective quotientAction
  primitive_index_lower : leastIndex ^ factorCount ≤ r
  outerOrder_log_bound :
    (outerOrder : ℝ) ≤ 3 * Real.logb 2 leastIndex

attribute [instance] PrimitiveSemisimpleOuterLogProfile.E_normal

namespace PrimitiveSemisimpleOuterLogProfile

variable {L : Type} [Group L] {r : ℕ}
  (C : PrimitiveSemisimpleOuterLogProfile L r)

/-- Replace the single logarithmic literature input by the two exact natural
inequalities consumed by the primitive compression API. -/
noncomputable def toCompressionProfile :
    PrimitiveSemisimpleCompressionProfile L r where
  E := C.E
  E_normal := C.E_normal
  chart := C.chart
  factorCount := C.factorCount
  factorCount_pos := C.factorCount_pos
  leastIndex := C.leastIndex
  leastIndex_two_le := (by norm_num : 2 ≤ 5).trans C.leastIndex_five_le
  outerOrder := C.outerOrder
  outerOrder_pos := C.outerOrder_pos
  quotientAction := C.quotientAction
  quotientAction_injective := C.quotientAction_injective
  primitive_index_lower := C.primitive_index_lower
  multiple_factor_base := primitive_outerOrder_square_bound
    C.leastIndex C.outerOrder C.leastIndex_five_le C.outerOrder_log_bound
  large_simple_base := fun hell => primitive_outerOrder_large_simple_bound
    C.leastIndex C.outerOrder hell C.outerOrder_log_bound

/-- The multi-factor certificate generated directly from the natural
outer-order profile. -/
noncomputable def multipleCertificate (ha : 2 ≤ C.factorCount) :
    PrimitiveSemisimpleCompressionCertificate L r :=
  .multiple C.toCompressionProfile ha

/-- The large almost-simple certificate generated directly from the natural
outer-order profile. -/
noncomputable def largeSimpleCertificate
    (ha : C.factorCount = 1) (hell : 30 ≤ C.leastIndex) :
    PrimitiveSemisimpleCompressionCertificate L r :=
  .largeSimple C.toCompressionProfile ha hell

end PrimitiveSemisimpleOuterLogProfile

end SymmetricSubgroupAsymptotics

end
