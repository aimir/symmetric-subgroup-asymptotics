import SymmetricSubgroupAsymptotics.QuadraticRankOrderCubeNumerics

/-! Scalar budgets for the orthogonal point-radical route. These statements
do not assert the separate natural-orbit or proper-index theorems. There
is no extra characteristic-prime multiplier in either index budget.
One exponent dominates the current B, D and twisted-D component bounds.
The binary rank-four orthogonal cases remain excluded explicitly. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.OrthogonalPointRadicalOrderCubeNumerics
open QuadraticRankOrderCubeNumerics

def componentExponent (r : ℕ) : ℕ := 2*r^2+3*r+6
def oddIndex (q r : ℕ) : ℕ := (q^(r-1)-1)*q^(r-1)
def minusIndex (q r : ℕ) : ℕ := (q^(r-2)-1)*q^(r-1)

private theorem exponent_double (r : ℕ) (hr : 3 ≤ r) :
    componentExponent (r+1) ≤ 2*componentExponent r := by
  unfold componentExponent
  nlinarith

private theorem large_field_star (q r : ℕ) (hq : 5 ≤ q) (hr : 3 ≤ r) :
    q^(3*componentExponent r) ≤ 5^(q^r-1) := by
  apply rank_tail q (by omega) componentExponent 3 exponent_double ?_ r hr
  exact field_tail 5 3 33 15 (by decide) (by decide +kernel) (by decide)
    (Nat.pow_le_pow_right (by decide) (by decide)) q hq

private theorem rank_five_star (q r : ℕ) (hq : 3 ≤ q) (hr : 5 ≤ r) :
    q^(3*componentExponent r) ≤ 5^(q^r-1) := by
  by_cases hlarge : 5 ≤ q
  · exact large_field_star q r hlarge (by omega)
  · have hqcases : q = 3 ∨ q = 4 := by omega
    rcases hqcases with rfl | rfl
    · exact rank_tail 3 (by decide) componentExponent 5
        (fun r hr => exponent_double r (by omega)) (by decide +kernel) r hr
    · apply rank_tail 4 (by decide) componentExponent 5
        (fun r hr => exponent_double r (by omega)) ?_ r hr
      exact (Nat.pow_le_pow_left (by decide : (4 : ℕ) ≤ 5) _).trans
        (Nat.pow_le_pow_right (by decide) (by decide))

private theorem star_le_product (q r a : ℕ) (hq : 2 ≤ q) (hr : 1 ≤ r) (ha : 2 ≤ a) :
    q^r ≤ (q^a-1)*q^(r-1) := by
  have hqa : q^2 ≤ q^a := Nat.pow_le_pow_right (by omega) ha
  have hq2 : q+1 ≤ q^2 := by nlinarith
  have hlo : q ≤ q^a-1 := by omega
  calc
    q^r = q*q^(r-1) := by rw [← pow_succ']; congr 1; omega
    _ ≤ (q^a-1)*q^(r-1) := Nat.mul_le_mul_right _ hlo

/-- The unmultiplied odd-dimensional natural orbit count pays the common
component exponent in every odd field and rank at least three. -/
theorem odd_order_cube (q r : ℕ) (hq : 3 ≤ q) (hr : 3 ≤ r) :
    q^(3*componentExponent r) ≤ 5^(oddIndex q r-1) := by
  have hstar : q^r ≤ oddIndex q r :=
    star_le_product q r (r-1) (by omega) (by omega) (by omega)
  by_cases hlarge : 5 ≤ q
  · exact (large_field_star q r hlarge hr).trans
      (Nat.pow_le_pow_right (by decide) (Nat.sub_le_sub_right hstar 1))
  · by_cases hr5 : 5 ≤ r
    · exact (rank_five_star q r hq hr5).trans
        (Nat.pow_le_pow_right (by decide) (Nat.sub_le_sub_right hstar 1))
    · have hqc : q = 3 ∨ q = 4 := by omega
      have hrc : r = 3 ∨ r = 4 := by omega
      rcases hqc with rfl | rfl <;> rcases hrc with rfl | rfl
      · exact (by decide +kernel)
      · exact (Nat.pow_le_pow_left (by decide : (3 : ℕ) ≤ 5) _).trans
          (Nat.pow_le_pow_right (by decide) (by decide))
      · exact (Nat.pow_le_pow_left (by decide : (4 : ℕ) ≤ 5) _).trans
          (Nat.pow_le_pow_right (by decide) (by decide))
      · exact (Nat.pow_le_pow_left (by decide : (4 : ℕ) ≤ 5) _).trans
          (Nat.pow_le_pow_right (by decide) (by decide))

/-- The smaller minus-type orbit count pays both even-dimensional
families in every odd field, uniformly from rank four. -/
theorem minus_odd_order_cube (q r : ℕ) (hq : 3 ≤ q) (hr : 4 ≤ r) :
    q^(3*componentExponent r) ≤ 5^(minusIndex q r-1) := by
  have hstar : q^r ≤ minusIndex q r :=
    star_le_product q r (r-2) (by omega) (by omega) (by omega)
  by_cases hlarge : 5 ≤ q
  · exact (large_field_star q r hlarge (by omega)).trans
      (Nat.pow_le_pow_right (by decide) (Nat.sub_le_sub_right hstar 1))
  · by_cases hr5 : 5 ≤ r
    · exact (rank_five_star q r hq hr5).trans
        (Nat.pow_le_pow_right (by decide) (Nat.sub_le_sub_right hstar 1))
    · have he : r = 4 := by omega
      subst r
      have hqc : q = 3 ∨ q = 4 := by omega
      rcases hqc with rfl | rfl
      · exact (Nat.pow_le_pow_left (by decide : (3 : ℕ) ≤ 5) _).trans
          (Nat.pow_le_pow_right (by decide) (by decide))
      · exact (Nat.pow_le_pow_left (by decide : (4 : ℕ) ≤ 5) _).trans
          (Nat.pow_le_pow_right (by decide) (by decide))

/-- Binary rank four is deliberately absent. The exact binary rank-five
seed and the common tail pay every larger rank. -/
theorem minus_binary_order_cube (r : ℕ) (hr : 5 ≤ r) :
    (2 : ℕ)^(3*componentExponent r) ≤ 5^(minusIndex 2 r-1) := by
  by_cases hr8 : 8 ≤ r
  · have hs : (2 : ℕ)^(3*componentExponent r) ≤ 5^(2^r-1) := by
      apply rank_tail 2 (by decide) componentExponent 8
        (fun r hr => exponent_double r (by omega)) ?_ r hr8
      exact (by decide +kernel)
    exact hs.trans (Nat.pow_le_pow_right (by decide)
      (Nat.sub_le_sub_right (star_le_product 2 r (r-2) (by decide) (by omega) (by omega)) 1))
  · have hrc : r = 5 ∨ r = 6 ∨ r = 7 := by omega
    rcases hrc with rfl | rfl | rfl
    · exact (by decide +kernel)
    · exact (Nat.pow_le_pow_left (by decide : (2 : ℕ) ≤ 5) _).trans
        (Nat.pow_le_pow_right (by decide) (by decide))
    · exact (Nat.pow_le_pow_left (by decide : (2 : ℕ) ≤ 5) _).trans
        (Nat.pow_le_pow_right (by decide) (by decide))

end SymmetricSubgroupAsymptotics.OrthogonalPointRadicalOrderCubeNumerics
