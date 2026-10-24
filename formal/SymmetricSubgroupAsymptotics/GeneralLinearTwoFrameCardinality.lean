import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Algebra.BigOperators.Fin

/-! Exact two-frame cancellation for the actual general linear group.
The complement factor is the full actual GL of dimension n-2; no
classical-form nondegeneracy or isometry classification is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics.GeneralLinearTwoFrameCardinality

def orderProduct (q n : ℕ) : ℕ := ∏ i : Fin n, (q ^ n - q ^ i.val)

theorem orderProduct_add_two (q n : ℕ) :
    orderProduct q (n + 2) =
      (q ^ (n + 2) - 1) * (q ^ (n + 2) - q) *
        q ^ (2 * n) * orderProduct q n := by
  have hterm (i : Fin n) :
      q ^ (n + 2) - q ^ (i.val + 2) = q ^ 2 * (q ^ n - q ^ i.val) := by
    rw [Nat.mul_sub_left_distrib]
    congr 1 <;> rw [pow_add] <;> exact mul_comm _ _
  have hprod : (∏ i : Fin n, (q ^ (n + 2) - q ^ (i.val + 2))) =
      q ^ (2 * n) * ∏ i : Fin n, (q ^ n - q ^ i.val) := by
    calc
      _ = ∏ i : Fin n, (q ^ 2 * (q ^ n - q ^ i.val)) :=
        Finset.prod_congr rfl (fun i _ => hterm i)
      _ = (∏ _i : Fin n, q ^ 2) * ∏ i : Fin n, (q ^ n - q ^ i.val) :=
        Finset.prod_mul_distrib
      _ = _ := by
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
  unfold orderProduct
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
  simp only [Fin.val_zero, Fin.val_succ, zero_add, pow_zero, pow_one]
  change (q ^ (n + 2) - 1) * ((q ^ (n + 2) - q) *
    ∏ i : Fin n, (q ^ (n + 2) - q ^ (i.val + 2))) = _
  rw [hprod]
  ac_rfl

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Actual basis transport identifies the linear-equivalence cardinal with the GL product. -/
theorem linearEquiv_card_eq_orderProduct [Finite K] [Module.Finite K V] :
    Nat.card (V ≃ₗ[K] V) = orderProduct (Nat.card K) (Module.finrank K V) := by
  letI : Fintype K := Fintype.ofFinite K
  let b := Module.finBasis K V
  let e := (Matrix.GeneralLinearGroup.toLin' b).trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K V)
  calc
    _ = Nat.card (Matrix.GeneralLinearGroup (Fin (Module.finrank K V)) K) :=
      Nat.card_congr e.toEquiv.symm
    _ = _ := by
      simpa only [orderProduct, Nat.card_eq_fintype_card] using
        (Matrix.card_GL_field (𝔽 := K) (Module.finrank K V))

/-- The exact actual GL_n formula, with its two frame choices and full complement. -/
theorem generalLinear_card_add_two [Finite K] (n : ℕ) :
    Nat.card (Matrix.GeneralLinearGroup (Fin (n + 2)) K) =
      (Nat.card K ^ (n + 2) - 1) * (Nat.card K ^ (n + 2) - Nat.card K) *
        Nat.card K ^ (2 * n) * Nat.card (Matrix.GeneralLinearGroup (Fin n) K) := by
  letI : Fintype K := Fintype.ofFinite K
  have hc (k : ℕ) : Nat.card (Matrix.GeneralLinearGroup (Fin k) K) =
      orderProduct (Nat.card K) k := by
    simpa only [orderProduct, Nat.card_eq_fintype_card] using
      (Matrix.card_GL_field (𝔽 := K) k)
  rw [hc, hc, orderProduct_add_two]

end SymmetricSubgroupAsymptotics.GeneralLinearTwoFrameCardinality
