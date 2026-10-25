import Mathlib.Tactic

/-! A uniform binary small-fibre budget for the separated-cut partition
envelope. The factor eight retains the actual alternating/outer class
charge. This is arithmetic only; a partition count is not assumed or
asserted here. The five-step recurrence has one integer-power seed. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.AlternatingSmallFibrePartitionTailNumerics

def envelope (n : ℕ) : ℕ := 2^n*8*(n+1)^4*6^((n+4)/5)

theorem envelope_mono {m n : ℕ} (h : m≤n) : envelope m≤envelope n := by
  apply Nat.mul_le_mul
  · apply Nat.mul_le_mul
    · exact Nat.mul_le_mul_right 8 (Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) h)
    · exact Nat.pow_le_pow_left (by omega) 4
  · exact Nat.pow_le_pow_right (by decide : 0<(6:ℕ))
      (Nat.div_le_div_right (Nat.add_le_add_right h 4))

theorem envelope_cube (n : ℕ) : envelope n^3 =
    (2^(3*n)*8^3*6^(3*((n+4)/5)))*(n+1)^12 := by
  simp only [envelope,mul_pow,←pow_mul]
  rw [Nat.mul_comm n 3,Nat.mul_comm ((n+4)/5) 3]
  norm_num only
  ring

private theorem polynomial_step (n : ℕ) (hn : 199≤n) :
    2^15*6^3*(n+6)^12≤5^10*(n+1)^12 := by
  have hl : 40*(n+6)≤41*(n+1) := by omega
  have hp := Nat.pow_le_pow_left hl 12
  rw [mul_pow,mul_pow] at hp
  have hc : (2:ℕ)^15*6^3*41^12≤5^10*40^12 := by decide +kernel
  have hh : 40^12*(2^15*6^3*(n+6)^12)≤40^12*(5^10*(n+1)^12) := by
    calc
      _ = (2^15*6^3)*(40^12*(n+6)^12) := by ring
      _ ≤ (2^15*6^3)*(41^12*(n+1)^12) := Nat.mul_le_mul_left _ hp
      _ = (2^15*6^3*41^12)*(n+1)^12 := by ring
      _ ≤ (5^10*40^12)*(n+1)^12 := Nat.mul_le_mul_right _ hc
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left hh (by decide : 0<(40:ℕ)^12)

theorem envelope_cube_step (n : ℕ) (hn : 199≤n) :
    envelope (n+5)^3≤5^10*envelope n^3 := by
  have hceil : (n+5+4)/5=(n+4)/5+1 := by omega
  rw [envelope_cube,envelope_cube,hceil]
  have h2 : 3*(n+5)=3*n+15 := by omega
  have h6 : 3*((n+4)/5+1)=3*((n+4)/5)+3 := by omega
  rw [h2,h6,pow_add,pow_add]
  calc
    _ = (2^(3*n)*8^3*6^(3*((n+4)/5)))*(2^15*6^3*(n+6)^12) := by
      rw [show n+5+1=n+6 by omega]
      ac_rfl
    _ ≤ (2^(3*n)*8^3*6^(3*((n+4)/5)))*(5^10*(n+1)^12) :=
      Nat.mul_le_mul_left _ (polynomial_step n hn)
    _ = _ := by ring

private theorem envelope_cube_blocks (q : ℕ) (hq : 819≤q) (r : ℕ) (hr : r<5) :
    envelope (5*q+r)^3≤5^(2*(5*q+r)-1) := by
  induction q,hq using Nat.le_induction with
  | base =>
    have hexp : 8189≤2*(5*819+r)-1 := by omega
    have hsmall : 5*819+r≤4099 := by omega
    have hseed : envelope 4099^3≤5^8189 := by decide +kernel
    have hh := (Nat.pow_le_pow_left (envelope_mono hsmall) 3).trans hseed
    exact hh.trans (Nat.pow_le_pow_right (by decide : 0<(5:ℕ)) hexp)
  | succ q hq ih =>
    have hn : 199≤5*q+r := by omega
    have he : 5*(q+1)+r=(5*q+r)+5 := by omega
    calc
      envelope (5*(q+1)+r)^3 = envelope ((5*q+r)+5)^3 := by rw [he]
      _ ≤ 5^10*envelope (5*q+r)^3 := envelope_cube_step _ hn
      _ ≤ 5^10*5^(2*(5*q+r)-1) := Nat.mul_le_mul_left _ ih
      _ = 5^(2*(5*(q+1)+r)-1) := by rw [←pow_add];congr 1;omega

theorem binary_partition_envelope_cube_le (n : ℕ) (hn : 4096≤n) :
    (2^n*8*(n+1)^4*6^((n+4)/5))^3≤5^(2*n-1) := by
  have hq : 819≤n/5 := by omega
  have hr : n%5<5 := Nat.mod_lt n (by decide)
  have he : 5*(n/5)+n%5=n := by omega
  simpa only [he,envelope] using envelope_cube_blocks (n/5) hq (n%5) hr

theorem ternary_partition_envelope_cube_le (n : ℕ) (hn : 4096≤n) :
    (3^n*8*(n+1)^4*6^((n+4)/5))^3≤5^(3*n-1) := by
  let T : ℕ := 8*(n+1)^4*6^((n+4)/5)
  have hb : (2^n*T)^3≤5^(2*n-1) := by
    simpa only [T,Nat.mul_assoc] using binary_partition_envelope_cube_le n hn
  have h3 : ((3 : ℕ)^n)^3=27^n := by
    rw [←pow_mul,Nat.mul_comm n 3,pow_mul]
    norm_num
  have h2 : ((2 : ℕ)^n)^3=8^n := by
    rw [←pow_mul,Nat.mul_comm n 3,pow_mul]
    norm_num
  have hfinal : (3^n*T)^3≤5^(3*n-1) := by
    calc
      (3^n*T)^3=27^n*T^3 := by rw [mul_pow,h3]
      _ ≤ 40^n*T^3 := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by decide) n)
      _ = (2^n*T)^3*5^n := by
        rw [show (40 : ℕ)=8*5 by decide,mul_pow]
        conv_rhs => rw [mul_pow,h2]
        ring
      _ ≤ 5^(2*n-1)*5^n := Nat.mul_le_mul_right _ hb
      _ = 5^(3*n-1) := by rw [←pow_add]; congr 1; omega
  simpa only [T,Nat.mul_assoc] using hfinal

end SymmetricSubgroupAsymptotics.AlternatingSmallFibrePartitionTailNumerics
