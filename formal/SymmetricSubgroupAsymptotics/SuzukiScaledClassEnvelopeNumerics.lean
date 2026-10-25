import SymmetricSubgroupAsymptotics.SuzukiQuadraticTorusClassNumerics

/-! The exact Suzuki order-times-field-exponent ceiling pays the
scaled class envelope at every quadratic/torus index beyond its first
parameter. One polynomial-to-exponential induction handles the tail. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.SuzukiScaledClassEnvelopeNumerics
open SuzukiQuadraticTorusClassNumerics

theorem scaled_component_cube_tail (m : ℕ) (hm : 2 ≤ m) :
    25*(orderBound (fieldOrder m)*(2*m+1))^3 ≤ 3^(indexBound m) := by
  have hq : 32 ≤ fieldOrder m :=
    Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) (by omega : 5 ≤ 2*m+1)
  have he : 8 ≤ 2^(m+1) :=
    Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) (by omega : 3 ≤ m+1)
  have hb : 128 ≤ indexBound m := by
    have hh := Nat.mul_le_mul (by omega : 31 ≤ fieldOrder m-1) he
    change 128 ≤ (fieldOrder m-1)*2^(m+1)
    omega
  have hf : 2*m+1 ≤ fieldOrder m := (2*m+1).lt_two_pow_self.le
  have hcomponent : orderBound (fieldOrder m)*(2*m+1) ≤ fieldOrder m^6 :=
    (Nat.mul_le_mul (order_le_fifth _ (by omega)) hf).trans_eq (by ring)
  calc
    25*(orderBound (fieldOrder m)*(2*m+1))^3 ≤ 25*(fieldOrder m^6)^3 :=
      Nat.mul_le_mul_left 25 (Nat.pow_le_pow_left hcomponent 3)
    _ = 25*fieldOrder m^18 := by rw [←pow_mul]
    _ ≤ 25*indexBound m^18 := Nat.mul_le_mul_left 25
      (Nat.pow_le_pow_left (field_le_index m (by omega)) 18)
    _ ≤ 3^(indexBound m-1) :=
      RankOneSharpOrderCubeNumerics.polynomial_tail 25 18 3 128
        (by decide) (by decide +kernel) (by decide +kernel) (indexBound m) hb
    _ ≤ 3^(indexBound m) := Nat.pow_le_pow_right (by decide) (by omega)

end SymmetricSubgroupAsymptotics.SuzukiScaledClassEnvelopeNumerics
