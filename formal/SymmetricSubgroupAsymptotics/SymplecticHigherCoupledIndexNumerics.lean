import SymmetricSubgroupAsymptotics.SymplecticSharpOrderCubeNumerics

/-! A uniform higher-rank symplectic component cube for the coupled
proper-index lower bound. It reuses the existing rank/field tail with
twice the root-space dimension. The single smallest numerical seed is
checked by the kernel; no action or group is enumerated. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.SymplecticHigherCoupledIndexNumerics
open SymplecticSharpOrderCubeNumerics

theorem component_order_cube (q r : ℕ) (hq : 3 ≤ q) (hr : 3 ≤ r) :
    q^(3*(2*r^2+r+3)) ≤ 5^(3*q^(2*r-2)-1) := by
  by_cases hsmall : r = 3 ∧ q = 3
  · rcases hsmall with ⟨rfl, rfl⟩
    change (3 : ℕ)^72 ≤ 5^242
    decide
  · have ht : 4 ≤ 2*r-2 := by omega
    have hcap : Capacity q (2*r-2) := by
      by_cases hqfour : 4 ≤ q
      · exact Or.inr (Or.inr (Or.inl ⟨hqfour, ht⟩))
      · have hrank : 4 ≤ r := by omega
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hq, by omega⟩)))
    have hrank : r ≤ 2*r-2+1 := by omega
    have hsquare := Nat.pow_le_pow_left hrank 2
    have he : 2*r^2+r+3 ≤ componentExponent (2*r-2) := by
      unfold componentExponent
      omega
    have htail := common_order_cube q (2*r-2) (by omega) (by omega) hcap
    exact ((Nat.pow_le_pow_right (by omega : 0 < q) (Nat.mul_le_mul_left 3 he)).trans htail).trans
      (Nat.pow_le_pow_right (by decide) (by omega))

theorem coupled_index_ge_thirtyTwo (q r : ℕ) (hq : 3 ≤ q) (hr : 3 ≤ r) :
    32 ≤ 3*q^(2*r-2) := by
  have hp : (3 : ℕ)^4 ≤ q^(2*r-2) :=
    (Nat.pow_le_pow_left hq 4).trans (Nat.pow_le_pow_right (by omega) (by omega))
  omega

end SymmetricSubgroupAsymptotics.SymplecticHigherCoupledIndexNumerics
