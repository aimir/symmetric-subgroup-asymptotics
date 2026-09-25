import SymmetricSubgroupAsymptotics.PrimeCharacterGenerators
import Mathlib.GroupTheory.GroupAction.Primitive
import Mathlib.Data.Nat.Log

/-! The entire primitive degree≥34 three-twentieths tail.

The sole literature input is the normal-subgroup specialization of
Holt–Roney-Dougal, "Minimal and random generation of permutation and matrix
groups", J. Algebra387 (2013), Theorem1.1, p.1. The published theorem bounds
the generator number of every subnormal subgroup of a primitive group by
log₂ of its degree, except the degree3 S3 case. We use only actual normal
subgroups and degrees≥4; taking the integer part gives the stated input.
The relative-head comparison and all infinite-tail arithmetic are proved
here. No finite classification or three-twentieths conclusion is assumed.
-/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

def PrimitiveNormalGeneratorInput : Prop :=
  ∀ (w : ℕ),4≤w → ∀ (U : Subgroup (Equiv.Perm (Fin w))),
    MulAction.IsPreprimitive U (Fin w) → ∀ (N : Subgroup U),N.Normal →
      Group.rank N≤Nat.log2 w

theorem c1_log_tail_power (k : ℕ) : 20*(k+6)<3*2^(k+6) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    have hp : 2^(k+1+6)=2^(k+6)*2 := by rw [show k+1+6=k+6+1 by omega,pow_succ]
    rw [show k.succ+6=k+1+6 by omega,hp]
    nlinarith

theorem c1_primitive_log_tail (w : ℕ) (hw : 34≤w) : 20*Nat.log2 w<3*w := by
  rw [Nat.log2_eq_log_two]
  have hw0 : w≠0 := by omega
  by_cases hw64 : w<64
  · have hlog : Nat.log 2 w<6 :=
      (Nat.log_lt_iff_lt_pow (by decide : 1<2) hw0).mpr (by norm_num;exact hw64)
    omega
  · have hlog : 6≤Nat.log 2 w :=
      (Nat.le_log_iff_pow_le (by decide : 1<2) hw0).mpr (by norm_num;omega)
    obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le hlog
    have hp : 2^(Nat.log 2 w)≤w :=
      (Nat.le_log_iff_pow_le (by decide : 1<2) hw0).mp le_rfl
    have ht := c1_log_tail_power k
    have ht' : 20*Nat.log 2 w<3*2^(Nat.log 2 w) := by
      rw [hk,Nat.add_comm 6 k]
      exact ht
    exact ht'.trans_le (Nat.mul_le_mul_left 3 hp)

/-- Every actual primitive normal pair in degree≥34 is strictly below
the high-c1 threshold, assuming only the permitted published input. -/
theorem c1_primitive_relative_tail (hgen : PrimitiveNormalGeneratorInput)
    (w : ℕ) (hw : 34≤w) (U : Subgroup (Equiv.Perm (Fin w)))
    (hprim : MulAction.IsPreprimitive U (Fin w)) (N : Subgroup U) [N.Normal] :
    20*Module.finrank (ZMod 3) (primeRelativeCharacters 3 N)<3*w := by
  have hr := (primeRelativeHead_le_groupRank 3 N).trans
    (hgen w (by omega) U hprim N inferInstance)
  exact (Nat.mul_le_mul_left 20 hr).trans_lt (c1_primitive_log_tail w hw)

end SymmetricSubgroupAsymptotics
