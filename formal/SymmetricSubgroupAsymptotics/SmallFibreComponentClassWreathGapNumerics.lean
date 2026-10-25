import SymmetricSubgroupAsymptotics.ComponentOrderCubeWreathNumerics

/-! Shared numerical reserves for an actual binary or ternary block
action. The component class quantity B, every socle factor, the full
factorial and the lower bound on the ACTUAL top degree are retained.
There is no assertion about an unproved model capacity or a short-index
action. The scalar input deliberately allows B^3 <= 5^(b+1). -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.SmallFibreComponentClassWreathGapNumerics

private theorem factorial_exponent_room (b k : ℕ) (hb : 5 ≤ b) (hk : 2 ≤ k) :
    2*(b+1)+4*k ≤ (b-1)*b^k := by
  induction k,hk using Nat.le_induction with
  | base =>
    have hs : 5*b ≤ b^2 := by
      simpa only [pow_two,Nat.mul_comm] using Nat.mul_le_mul_right b hb
    have hh : 4*(5*b) ≤ (b-1)*b^2 :=
      Nat.mul_le_mul (by omega : 4 ≤ b-1) hs
    nlinarith
  | succ k hk ih =>
    calc
      2*(b+1)+4*(k+1) ≤ 2*(2*(b+1)+4*k) := by omega
      _ ≤ 2*((b-1)*b^k) := Nat.mul_le_mul_left 2 ih
      _ ≤ b*((b-1)*b^k) := Nat.mul_le_mul_right _ (by omega : 2 ≤ b)
      _ = (b-1)*b^(k+1) := by rw [pow_succ]; ring

private theorem square_scaled_envelope (b : ℕ) (hb : 5 ≤ b) :
    25*5^(2*(b+1))*(Nat.factorial 2)^3 ≤ 3^(b^2) := by
  induction b,hb using Nat.le_induction with
  | base => norm_num
  | succ b hb ih =>
    calc
      25*5^(2*(b+1+1))*(Nat.factorial 2)^3 =
          25*(25*5^(2*(b+1))*(Nat.factorial 2)^3) := by
        rw [show 2*(b+1+1)=2*(b+1)+2 by omega,pow_add]
        ring
      _ ≤ 25*3^(b^2) := Nat.mul_le_mul_left 25 ih
      _ ≤ 3^3*3^(b^2) := Nat.mul_le_mul_right _ (by decide : (25:ℕ) ≤ 3^3)
      _ = 3^(b^2+3) := by rw [pow_add]; ring
      _ ≤ 3^((b+1)^2) := Nat.pow_le_pow_right (by decide) (by nlinarith)

private theorem factorial_scaled_envelope (b k : ℕ) (hb : 5 ≤ b) (hk : 2 ≤ k) :
    25*5^(k*(b+1))*k.factorial^3 ≤ 3^(b^k) := by
  induction k,hk using Nat.le_induction with
  | base => exact square_scaled_envelope b hb
  | succ k hk ih =>
    have hr := factorial_exponent_room b k hb hk
    have hsub : b-1+1=b := by omega
    have hexp : b^k+2*(b+1+2*k) ≤ b^(k+1) := by
      calc
        b^k+2*(b+1+2*k) = b^k+(2*(b+1)+4*k) := by ring
        _ ≤ b^k+(b-1)*b^k := Nat.add_le_add_left hr _
        _ = (b-1+1)*b^k := by ring
        _ = b^(k+1) := by rw [hsub,pow_succ]; ring
    calc
      25*5^((k+1)*(b+1))*(k+1).factorial^3 =
          (25*5^(k*(b+1))*k.factorial^3)*5^(b+1)*(k+1)^3 := by
        rw [show (k+1)*(b+1)=k*(b+1)+(b+1) by ring,pow_add,
          Nat.factorial_succ,mul_pow]
        ring
      _ ≤ 3^(b^k)*5^(b+1)*5^(2*k) :=
        Nat.mul_le_mul (Nat.mul_le_mul_right _ ih)
          (ComponentOrderCubeWreathNumerics.factorial_step_cube_le k)
      _ = 3^(b^k)*5^(b+1+2*k) := by rw [mul_assoc,←pow_add]
      _ ≤ 3^(b^k)*(3^2)^(b+1+2*k) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by decide : (5:ℕ) ≤ 3^2) _)
      _ = 3^(b^k+2*(b+1+2*k)) := by rw [←pow_mul,←pow_add]
      _ ≤ 3^(b^(k+1)) := Nat.pow_le_pow_right (by decide) hexp

private theorem component_scaled_envelope (B b k : ℕ)
    (hb : 5 ≤ b) (hk : 2 ≤ k) (hB : B^3 ≤ 5^(b+1)) :
    25*(B^k*k.factorial)^3 ≤ 3^(b^k) := by
  have he : (B^k)^3=(B^3)^k := by
    rw [←pow_mul,←pow_mul,Nat.mul_comm k 3]
  calc
    25*(B^k*k.factorial)^3 = 25*(B^3)^k*k.factorial^3 := by
      rw [mul_pow,he]
      ring
    _ ≤ 25*(5^(b+1))^k*k.factorial^3 :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hB k))
    _ = 25*5^(k*(b+1))*k.factorial^3 := by
      rw [←pow_mul,Nat.mul_comm (b+1) k]
    _ ≤ 3^(b^k) := factorial_scaled_envelope b k hb hk

private theorem binary_gap_of_scaled_envelope (n E : ℕ) (hn : 1 ≤ n)
    (hE : 25*E^3 ≤ 3^n) : (2^n*E)^3 ≤ 5^(2*n-2) := by
  have htwo : (2^n)^3=8^n := by
    rw [←pow_mul,Nat.mul_comm n 3,pow_mul]
    norm_num
  have hscaled : 25*(2^n*E)^3 ≤ 25^n := by
    calc
      25*(2^n*E)^3 = 8^n*(25*E^3) := by rw [mul_pow,htwo]; ring
      _ ≤ 8^n*3^n := Nat.mul_le_mul_left _ hE
      _ = 24^n := by rw [←mul_pow]; norm_num
      _ ≤ 25^n := Nat.pow_le_pow_left (by decide) n
  have he : 25*5^(2*n-2)=25^n := by
    calc
      25*5^(2*n-2) = 5^(2*n) := by
        rw [show (25:ℕ)=5^2 by decide,←pow_add]
        congr 1
        omega
      _ = (5^2)^n := pow_mul 5 2 n
      _ = 25^n := by norm_num
  rw [←he] at hscaled
  exact Nat.le_of_mul_le_mul_left hscaled (by decide)

private theorem ternary_gap_of_binary (n E : ℕ) (hn : 2 ≤ n)
    (hbinary : (2^n*E)^3 ≤ 5^(2*n-2)) :
    (3^n*E)^3 ≤ 5^(3*n-2) := by
  have hthree : (3^n)^3=27^n := by
    rw [←pow_mul,Nat.mul_comm n 3,pow_mul]
    norm_num
  have htwo : (2^n)^3=8^n := by
    rw [←pow_mul,Nat.mul_comm n 3,pow_mul]
    norm_num
  have h27 : (3^n)^3 ≤ 5^n*(2^n)^3 := by
    rw [hthree,htwo,←mul_pow]
    exact Nat.pow_le_pow_left (by decide : (27:ℕ) ≤ 5*8) n
  calc
    (3^n*E)^3 = (3^n)^3*E^3 := mul_pow _ _ _
    _ ≤ (5^n*(2^n)^3)*E^3 := Nat.mul_le_mul_right _ h27
    _ = 5^n*(2^n*E)^3 := by rw [mul_pow]; ring
    _ ≤ 5^n*5^(2*n-2) := Nat.mul_le_mul_left _ hbinary
    _ = 5^(3*n-2) := by rw [←pow_add]; congr 1; omega

theorem binary_multi_product_cube_gap (B b k n : ℕ)
    (hb : 5 ≤ b) (hk : 2 ≤ k) (hB : B^3 ≤ 5^(b+1)) (hdegree : b^k ≤ n) :
    (2^n*(B^k*k.factorial))^3 ≤ 5^(2*n-2) := by
  have hp : b ≤ b^k := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0 < b)
      (by omega : 1 ≤ k)
  apply binary_gap_of_scaled_envelope n _ (by omega)
  exact (component_scaled_envelope B b k hb hk hB).trans
    (Nat.pow_le_pow_right (by decide) hdegree)

theorem ternary_multi_product_cube_gap (B b k n : ℕ)
    (hb : 5 ≤ b) (hk : 2 ≤ k) (hB : B^3 ≤ 5^(b+1)) (hdegree : b^k ≤ n) :
    (3^n*(B^k*k.factorial))^3 ≤ 5^(3*n-2) := by
  have hp : b ≤ b^k := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0 < b)
      (by omega : 1 ≤ k)
  exact ternary_gap_of_binary n _ (by omega)
    (binary_multi_product_cube_gap B b k n hb hk hB hdegree)

private theorem far_scaled_envelope (b : ℕ) (hb : 5 ≤ b) :
    25*5^(b+1) ≤ 3^(2*b+2) := by
  induction b,hb using Nat.le_induction with
  | base => norm_num
  | succ b hb ih =>
    calc
      25*5^(b+1+1) = 5*(25*5^(b+1)) := by rw [pow_succ]; ring
      _ ≤ 5*3^(2*b+2) := Nat.mul_le_mul_left _ ih
      _ ≤ 3^2*3^(2*b+2) := Nat.mul_le_mul_right _ (by decide : (5:ℕ) ≤ 3^2)
      _ = 3^(2*(b+1)+2) := by
        rw [←pow_add]
        congr 1
        omega

theorem binary_far_product_cube_gap (B b n : ℕ)
    (hb : 5 ≤ b) (hB : B^3 ≤ 5^(b+1)) (hdegree : 2*b+2 ≤ n) :
    (2^n*B)^3 ≤ 5^(2*n-2) := by
  apply binary_gap_of_scaled_envelope n B (by omega)
  exact ((Nat.mul_le_mul_left 25 hB).trans (far_scaled_envelope b hb)).trans
    (Nat.pow_le_pow_right (by decide) hdegree)

theorem ternary_far_product_cube_gap (B b n : ℕ)
    (hb : 5 ≤ b) (hB : B^3 ≤ 5^(b+1)) (hdegree : 2*b+2 ≤ n) :
    (3^n*B)^3 ≤ 5^(3*n-2) :=
  ternary_gap_of_binary n B (by omega)
    (binary_far_product_cube_gap B b n hb hB hdegree)

end SymmetricSubgroupAsymptotics.SmallFibreComponentClassWreathGapNumerics
