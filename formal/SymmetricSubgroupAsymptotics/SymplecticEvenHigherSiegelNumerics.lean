import SymmetricSubgroupAsymptotics.SymplecticSharpOrderCubeNumerics

/-! Scalar budgets for a uniform characteristic-two Siegel index
argument. These numerical statements do not assert the still separate
group-theoretic index theorem. The field-two low-rank exceptions are
retained explicitly. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.SymplecticEvenHigherSiegelNumerics
open SymplecticSharpOrderCubeNumerics

def binaryIndexLower (r : ℕ) : ℕ := 2^(r-3)*(2^r-2)

theorem field_four_order_cube (q r : ℕ) (hq : 4 ≤ q) (hr : 3 ≤ r) :
    q^(3*(2*r^2+r+3)) ≤ 5^(q^(2*r-2)-1) := by
  have ht : 4 ≤ 2*r-2 := by omega
  have hc : Capacity q (2*r-2) := Or.inr (Or.inr (Or.inl ⟨hq, ht⟩))
  have hrank : r ≤ 2*r-2+1 := by omega
  have hs := Nat.pow_le_pow_left hrank 2
  have he : 2*r^2+r+3 ≤ componentExponent (2*r-2) := by
    unfold componentExponent
    omega
  exact (Nat.pow_le_pow_right (by omega : 0 < q) (Nat.mul_le_mul_left 3 he)).trans
    (common_order_cube q (2*r-2) (by omega) (by omega) hc)

theorem binary_index_ge_power (r : ℕ) (hr : 5 ≤ r) :
    2^(2*r-4) ≤ binaryIndexLower r := by
  have he : r-1+1 = r := by omega
  have htwo : 2 ≤ (2 : ℕ)^(r-1) :=
    (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 1 ≤ r-1))
  have hp : (2 : ℕ)^r = 2^(r-1)*2 := by rw [← pow_succ, he]
  have hhalf : (2 : ℕ)^(r-1) ≤ 2^r-2 := by omega
  have hexp : 2*r-4 = (r-3)+(r-1) := by omega
  unfold binaryIndexLower
  rw [hexp, pow_add]
  exact Nat.mul_le_mul_left _ hhalf

theorem binary_order_cube (r : ℕ) (hr : 5 ≤ r) :
    (2 : ℕ)^(3*(2*r^2+r+3)) ≤ 5^(binaryIndexLower r-1) := by
  by_cases hfive : r = 5
  · subst r
    change (2 : ℕ)^174 ≤ 5^119
    calc
      (2 : ℕ)^174 = (2^3)^58 := by rw [← pow_mul]
      _ ≤ (5^2)^58 := Nat.pow_le_pow_left (by decide : (2 : ℕ)^3 ≤ 5^2) 58
      _ = 5^116 := by rw [← pow_mul]
      _ ≤ 5^119 := Nat.pow_le_pow_right (by decide) (by decide)
  · have ht : 8 ≤ 2*r-4 := by omega
    have hc : Capacity 2 (2*r-4) := Or.inr (Or.inr (Or.inr (Or.inr ht)))
    have hrank : r ≤ 2*r-4+1 := by omega
    have hs := Nat.pow_le_pow_left hrank 2
    have he : 2*r^2+r+3 ≤ componentExponent (2*r-4) := by
      unfold componentExponent
      omega
    exact ((Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ))
      (Nat.mul_le_mul_left 3 he)).trans
      (common_order_cube 2 (2*r-4) (by decide) (by omega) hc)).trans
      (Nat.pow_le_pow_right (by decide) (Nat.sub_le_sub_right (binary_index_ge_power r hr) 1))

end SymmetricSubgroupAsymptotics.SymplecticEvenHigherSiegelNumerics
