import SymmetricSubgroupAsymptotics.CFSGTypeAGeneralLinearCardBound
import Lean.Elab.Tactic.Omega

/-! A uniform lower bound for the actual SL middle of an opposite block
cell. This follows from the checked GL product count and determinant
kernel inequality; no orthogonal or symplectic order formula is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBIndexSLCard
variable (K : Type) [Field K] [Finite K]

theorem specialLinear_card_lower (r : ℕ) (hr : 0 < r) :
    Nat.card K ^ (r * (r - 1)) * (Nat.card K - 1) ^ (r - 1) ≤
      Nat.card (Matrix.SpecialLinearGroup (Fin r) K) := by
  letI := Fintype.ofFinite K
  let q := Nat.card K
  have hq : 1 < q := Finite.one_lt_card (α := K)
  have hfactor (i : Fin r) : q ^ (r - 1) * (q - 1) ≤ q ^ r - q ^ i.val := by
    have hi : i.val ≤ r - 1 := by omega
    have hpow : q ^ i.val ≤ q ^ (r - 1) := Nat.pow_le_pow_right (by omega : 1 ≤ q) hi
    calc
      q ^ (r - 1) * (q - 1) = q ^ r - q ^ (r - 1) := by
        rw [Nat.mul_sub_left_distrib, mul_one, ← pow_succ]
        rw [Nat.sub_add_cancel (by omega : 1 ≤ r)]
      _ ≤ q ^ r - q ^ i.val := Nat.sub_le_sub_left hpow _
  have hprod : (q ^ (r - 1) * (q - 1)) ^ r ≤ ∏ i : Fin r, (q ^ r - q ^ i.val) := by
    have h : (∏ _i : Fin r, (q ^ (r - 1) * (q - 1))) ≤
        ∏ i : Fin r, (q ^ r - q ^ i.val) := Finset.prod_le_prod' (fun i _ => hfactor i)
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using h
  have hGL : q ^ (r * (r - 1)) * (q - 1) ^ r ≤
      Nat.card (Matrix.GeneralLinearGroup (Fin r) K) := by
    rw [Matrix.card_GL_field]
    have hcomm : (r - 1) * r = r * (r - 1) := Nat.mul_comm _ _
    simpa only [mul_pow, ← pow_mul, hcomm, q, Nat.card_eq_fintype_card] using hprod
  have hdet := CFSGTypeAGeneralLinearCardBound.generalLinear_card_le_specialLinear_mul_units
    (F := K) (n := Fin r)
  rw [Nat.card_units] at hdet
  have hbudget : (q ^ (r * (r - 1)) * (q - 1) ^ (r - 1)) * (q - 1) ≤
      Nat.card (Matrix.SpecialLinearGroup (Fin r) K) * (q - 1) := by
    calc
      _ = q ^ (r * (r - 1)) * (q - 1) ^ r := by
        rw [mul_assoc, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ r)]
      _ ≤ _ := hGL.trans hdet
  exact Nat.le_of_mul_le_mul_right hbudget (by omega : 0 < q - 1)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBIndexSLCard
