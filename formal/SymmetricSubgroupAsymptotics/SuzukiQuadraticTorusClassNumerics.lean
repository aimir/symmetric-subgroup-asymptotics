import SymmetricSubgroupAsymptotics.RankOneSharpOrderCubeNumerics

/-! Uniform order-cube capacity at the quadratic/torus proper-index
bound. This uses one exact smallest-parameter seed and one polynomial
tail; no conjugacy-class or finite action table is an input. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.SuzukiQuadraticTorusClassNumerics

def fieldOrder (m : ℕ) : ℕ := 2^(2*m+1)
def indexBound (m : ℕ) : ℕ := (fieldOrder m-1)*2^(m+1)
def orderBound (q : ℕ) : ℕ := q^2*(q-1)*(q^2+1)

theorem field_ge_eight (m : ℕ) (hm : 1 ≤ m) : 8 ≤ fieldOrder m :=
  Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 3 ≤ 2*m+1)

theorem field_le_index (m : ℕ) (hm : 1 ≤ m) : fieldOrder m ≤ indexBound m := by
  have hq := field_ge_eight m hm
  have hfour : 4 ≤ 2^(m+1) :=
    Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ m+1)
  have hmult := Nat.mul_le_mul_left (fieldOrder m-1) hfour
  change fieldOrder m ≤ (fieldOrder m-1)*2^(m+1)
  have hsub : fieldOrder m-1+1=fieldOrder m := by omega
  nlinarith

theorem index_ge_sixtyFour (m : ℕ) (hm : 2 ≤ m) : 64 ≤ indexBound m := by
  have hq : 32 ≤ fieldOrder m :=
    Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 5 ≤ 2*m+1)
  have he : 8 ≤ 2^(m+1) :=
    Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 3 ≤ m+1)
  have h := Nat.mul_le_mul (by omega : 31 ≤ fieldOrder m-1) he
  change 64 ≤ (fieldOrder m-1)*2^(m+1)
  omega

theorem order_le_fifth (q : ℕ) (hq : 1 ≤ q) : orderBound q ≤ q^5 := by
  have hsub : q-1+1=q := by omega
  have hq2 : q ≤ q^2+1 := by nlinarith
  have he : (q-1)*(q^2+1)+(q^2+1)=q^3+q := by
    calc
      _ = (q-1+1)*(q^2+1) := by ring
      _ = _ := by rw [hsub]; ring
  have hsmall : (q-1)*(q^2+1) ≤ q^3 := by omega
  calc
    orderBound q = q^2*((q-1)*(q^2+1)) := by unfold orderBound; ring
    _ ≤ q^2*q^3 := Nat.mul_le_mul_left _ hsmall
    _ = q^5 := by ring

theorem component_order_cube (m : ℕ) (hm : 1 ≤ m) :
    (orderBound (fieldOrder m)*(2*m+1))^3 ≤ 5^(indexBound m-1) := by
  by_cases hone : m=1
  · subst m
    decide +kernel
  · have hm2 : 2 ≤ m := by omega
    have hq : 1 ≤ fieldOrder m := (by decide : 1 ≤ 8).trans (field_ge_eight m hm)
    have hf : 2*m+1 ≤ fieldOrder m := (2*m+1).lt_two_pow_self.le
    have hprod : orderBound (fieldOrder m)*(2*m+1) ≤ fieldOrder m^6 := by
      exact (Nat.mul_le_mul (order_le_fifth _ hq) hf).trans_eq (by ring)
    calc
      (orderBound (fieldOrder m)*(2*m+1))^3 ≤ (fieldOrder m^6)^3 :=
        Nat.pow_le_pow_left hprod 3
      _ = fieldOrder m^18 := by ring
      _ ≤ indexBound m^18 := Nat.pow_le_pow_left (field_le_index m hm) 18
      _ ≤ 5^(indexBound m-1) := by
        have h := RankOneSharpOrderCubeNumerics.polynomial_tail 1 18 5 64
          (by decide) (by decide +kernel) (by decide +kernel)
          (indexBound m) (index_ge_sixtyFour m hm2)
        simpa only [one_mul] using h

end SymmetricSubgroupAsymptotics.SuzukiQuadraticTorusClassNumerics
