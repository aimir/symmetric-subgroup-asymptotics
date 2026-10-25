import SymmetricSubgroupAsymptotics.RankOneSharpClassCubeNumerics

/-! Shared scalar packets for actual prime-field and binary-power PSL2
bounds, plus two odd-power certificates. These are field parameters,
not actions or a subgroup census. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.PSLTwoImprovedScaledClassNumerics

theorem prime_field_tail (q : ℕ) (hq : 11≤q) : 25*(q+5)^3≤3^q := by
  induction q,hq using Nat.le_induction with
  | base => decide +kernel
  | succ q hq ih =>
    have hg : (q+6)^3≤3*(q+5)^3 := by nlinarith [Nat.zero_le (q^3),Nat.zero_le (q^2)]
    calc
      25*(q+1+5)^3≤25*(3*(q+5)^3) := Nat.mul_le_mul_left 25 (by simpa only [Nat.add_assoc] using hg)
      _=3*(25*(q+5)^3) := by ring
      _≤3*3^q := Nat.mul_le_mul_left 3 ih
      _=3^(q+1) := (pow_succ' 3 q).symm

theorem binary_power_tail (f : ℕ) (hf : 4≤f) :
    25*((2^f+4)*f)^3≤3^(2^f) := by
  induction f,hf using Nat.le_induction with
  | base => decide +kernel
  | succ f hf ih =>
    have hn : 16≤2^f := by
      simpa only [show (2:ℕ)^4=16 by decide] using Nat.pow_le_pow_right (by decide : 0<2) hf
    have hnf : 2^f≤2^f*f := Nat.le_mul_of_pos_right _ (by omega : 0<f)
    have hg : (2^(f+1)+4)*(f+1)≤4*((2^f+4)*f) := by
      rw [pow_succ]
      nlinarith
    have h64 : 64≤3^(2^f) := (by decide : 64≤3^4).trans
      (Nat.pow_le_pow_right (by decide) (by omega : 4≤2^f))
    calc
      25*((2^(f+1)+4)*(f+1))^3≤25*(4*((2^f+4)*f))^3 :=
        Nat.mul_le_mul_left 25 (Nat.pow_le_pow_left hg 3)
      _=64*(25*((2^f+4)*f)^3) := by ring
      _≤3^(2^f)*3^(2^f) := Nat.mul_le_mul h64 ih
      _=3^(2^(f+1)) := by
        rw [←pow_add,pow_succ]
        exact congrArg (fun n : ℕ => 3^n) (by omega)

theorem twentySeven : 25*((16:ℕ)*6)^3≤3^27 := by decide +kernel

theorem fortyNine : 25*((27:ℕ)*4)^3≤3^25 := by decide +kernel

end SymmetricSubgroupAsymptotics.PSLTwoImprovedScaledClassNumerics
