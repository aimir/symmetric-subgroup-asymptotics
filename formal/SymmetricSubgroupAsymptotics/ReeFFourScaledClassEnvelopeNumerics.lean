import SymmetricSubgroupAsymptotics.ReeFFourMiddleSuzukiClassNumerics

/-! The literal middle-Suzuki index pays the scaled binary/ternary
small-fibre packet from m=3. The two smaller positive parameters are
not covered by this estimate. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.ReeFFourScaledClassEnvelopeNumerics
open ReeFFourOrderCubeTailNumerics ReeFFourMiddleSuzukiClassNumerics

theorem scaled_field_cube (m : ℕ) (hm : 3 ≤ m) :
    25*fieldOrder m^81 ≤ 3^indexBound m := by
  induction m, hm using Nat.le_induction with
  | base => decide +kernel
  | succ m hm ih =>
    have hb := index_ge_248 m (by omega)
    have hs := indexBound_succ_ge_two m
    calc
      25*fieldOrder (m+1)^81 = 25*(4*fieldOrder m)^81 := by rw [fieldOrder_succ]
      _ = 4^81*(25*fieldOrder m^81) := by rw [mul_pow]; ring
      _ ≤ (3^2)^81*3^indexBound m :=
        Nat.mul_le_mul (Nat.pow_le_pow_left (by decide : (4 : ℕ) ≤ 3^2) 81) ih
      _ = 3^(162+indexBound m) := by rw [←pow_mul,←pow_add]
      _ ≤ 3^indexBound (m+1) :=
        Nat.pow_le_pow_right (by decide) (by omega)

theorem scaled_component_cube (m : ℕ) (hm : 3 ≤ m) :
    25*(fieldOrder m^26*(2*m+1))^3 ≤ 3^indexBound m := by
  have hf : 2*m+1 ≤ fieldOrder m := (2*m+1).lt_two_pow_self.le
  calc
    25*(fieldOrder m^26*(2*m+1))^3 ≤ 25*(fieldOrder m^26*fieldOrder m)^3 :=
      Nat.mul_le_mul_left 25 (Nat.pow_le_pow_left (Nat.mul_le_mul_left _ hf) 3)
    _ = 25*fieldOrder m^81 := by ring
    _ ≤ _ := scaled_field_cube m hm

end SymmetricSubgroupAsymptotics.ReeFFourScaledClassEnvelopeNumerics
