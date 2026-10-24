import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! A reusable polynomial-to-exponential tail from one exact seed and
one ratio comparison. The PSL2 component cube uses degree twelve and
starts at the actual half-field index 32. No field menu is enumerated. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.RankOneSharpOrderCubeNumerics

theorem polynomial_step (b d m₀ m : ℕ) (hm₀ : 0<m₀) (hm : m₀≤m)
    (hratio : (m₀+1)^d≤b*m₀^d) : (m+1)^d≤b*m^d := by
  have hlin : m₀*(m+1)≤(m₀+1)*m := by nlinarith
  have hp := Nat.pow_le_pow_left hlin d
  rw [mul_pow, mul_pow] at hp
  have hraw : m₀^d*(m+1)^d≤m₀^d*(b*m^d) := by
    calc
      m₀^d*(m+1)^d≤(m₀+1)^d*m^d := hp
      _ ≤(b*m₀^d)*m^d := Nat.mul_le_mul_right _ hratio
      _ =m₀^d*(b*m^d) := by ring
  exact Nat.le_of_mul_le_mul_left hraw (pow_pos hm₀ d)

theorem polynomial_tail (c d b m₀ : ℕ) (hm₀ : 0<m₀)
    (hratio : (m₀+1)^d≤b*m₀^d) (hbase : c*m₀^d≤b^(m₀-1))
    (m : ℕ) (hm : m₀≤m) : c*m^d≤b^(m-1) := by
  induction m, hm using Nat.le_induction with
  | base => exact hbase
  | succ m hm ih =>
    calc
      c*(m+1)^d≤c*(b*m^d) :=
        Nat.mul_le_mul_left _ (polynomial_step b d m₀ m hm₀ hm hratio)
      _ =b*(c*m^d) := by ring
      _ ≤b*b^(m-1) := Nat.mul_le_mul_left _ ih
      _ =b^((m+1)-1) := by
        rw [← pow_succ']
        congr 1
        omega

theorem order_cube_le (m : ℕ) (hm : 32≤m) : (8*m^4)^3≤5^(m-1) := by
  have h := polynomial_tail 512 12 5 32 (by decide)
    (by norm_num : (33:ℕ)^12≤5*32^12)
    (by norm_num : (512:ℕ)*32^12≤5^31) m hm
  convert h using 1 <;> ring

end SymmetricSubgroupAsymptotics.RankOneSharpOrderCubeNumerics
