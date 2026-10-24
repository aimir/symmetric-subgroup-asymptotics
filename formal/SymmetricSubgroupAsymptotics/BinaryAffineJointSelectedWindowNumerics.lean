import SymmetricSubgroupAsymptotics.NaturalSquareRootQuotientCeiling
import SymmetricSubgroupAsymptotics.PrimeGeneralLinearDefiningValuation
import Mathlib.Algebra.BigOperators.Fin

/-! Two selected scalar pilots for the joint actual GL-order charge.
All integer ceilings are connected to their real values by a proved
general theorem. These are numerical certificates, not group-row data
and not a claim that all remaining finite windows have been closed. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.BinaryAffineJointSelectedWindowNumerics
open NaturalSquareRootQuotientCeiling

def binaryGLOrder (d : ℕ) : ℕ := ∏ i ∈ Finset.range d, (2^d-2^i)

theorem matrix_GL_card_eq_order (d : ℕ) :
    Nat.card (Matrix.GeneralLinearGroup (Fin d) (ZMod 2)) = binaryGLOrder d := by
  have hh : Nat.card (Matrix.GeneralLinearGroup (Fin d) (ZMod 2)) =
      ∏ i : Fin d, (2^d-2^(i : ℕ)) := by
    simpa only [Fintype.card_eq_nat_card, Nat.card_zmod] using
      (Matrix.card_GL_field (𝔽 := ZMod 2) d)
  exact hh.trans (Fin.prod_univ_eq_prod_range (fun i : ℕ => 2^d-2^i) d)

def jointCost (d e : ℕ) : ℕ :=
  (d+d*(d-1)/2)*e.choose (e/2) +
    (Nat.log 2 (binaryGLOrder d)-d*(d-1)/2) + quotientCeiling (2^e) e

theorem jointCost_eq_actual (d e : ℕ) (he : 0 < e) :
    jointCost d e = (d+d*(d-1)/2)*e.choose (e/2) +
      (Nat.log 2 (Nat.card (Matrix.GeneralLinearGroup (Fin d) (ZMod 2)))-d*(d-1)/2) +
      ⌈(2 : ℝ)^e/Real.sqrt e⌉₊ := by
  simp only [jointCost, quotientCeiling_eq _ _ he, matrix_GL_card_eq_order,
    Nat.cast_pow, Nat.cast_ofNat]

theorem two_three : jointCost 2 3 ≤ quotientCeiling (2^(2+3)) (2+3) := by
  decide +kernel

theorem three_three : jointCost 3 3 ≤ quotientCeiling (2^(3+3)) (3+3) := by
  decide +kernel

end SymmetricSubgroupAsymptotics.BinaryAffineJointSelectedWindowNumerics
