import SymmetricSubgroupAsymptotics.CFSGTypeAMonomialRootAction

/-! Exact root and diagonal transport for matrix units. This version
uses no special-linear recognition and hence applies directly to the
actual elementary C subgroup inside the same matrix-unit group. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGMonomialUnitRootAction
open Matrix CFSGTypeAMonomialMatrices CFSGTypeAMonomialRootAction
variable {I : Type*} [Fintype I] [DecidableEq I] {K : Type*} [Field K]

def transvectionUnit (i j : I) (hij : i ≠ j) (a : K) : (Matrix I I K)ˣ where
  val := Matrix.transvection i j a
  inv := Matrix.transvection i j (-a)
  val_inv := by rw [Matrix.transvection_mul_transvection_same i j hij]; simp [Matrix.transvection]
  inv_val := by rw [Matrix.transvection_mul_transvection_same i j hij]; simp [Matrix.transvection]

@[simp] theorem transvectionUnit_val (i j : I) (hij : i ≠ j) (a : K) :
    (transvectionUnit i j hij a : Matrix I I K) = Matrix.transvection i j a := rfl

theorem monomial_conjugation (W : (Matrix I I K)ˣ) (σ : Equiv.Perm I)
    (d : I → K) (hW : (W : Matrix I I K) = monomial σ d)
    {i j : I} (hij : i ≠ j) (a : K) (hd : d (σ.symm j) ≠ 0) :
    W * transvectionUnit i j hij a * W⁻¹ =
      transvectionUnit (σ.symm i) (σ.symm j) (σ.symm.injective.ne hij)
        (d (σ.symm i) * a / d (σ.symm j)) := by
  have hm : W * transvectionUnit i j hij a =
      transvectionUnit (σ.symm i) (σ.symm j) (σ.symm.injective.ne hij)
        (d (σ.symm i) * a / d (σ.symm j)) * W := by
    apply Units.ext
    change (W : Matrix I I K) * Matrix.transvection i j a =
      Matrix.transvection (σ.symm i) (σ.symm j)
        (d (σ.symm i) * a / d (σ.symm j)) * (W : Matrix I I K)
    rw [hW]
    exact monomial_mul_transvection σ d i j a hd
  have hc := congrArg (fun X : (Matrix I I K)ˣ => X * W⁻¹) hm
  simpa only [mul_assoc, mul_inv_cancel, mul_one] using hc

theorem monomial_conjugation_diagonal (W : (Matrix I I K)ˣ) (σ : Equiv.Perm I)
    (d D : I → K) (hW : (W : Matrix I I K) = monomial σ d) :
    (W : Matrix I I K) * Matrix.diagonal D * (↑(W⁻¹) : Matrix I I K) =
      Matrix.diagonal (D ∘ σ) := by
  have hm : (W : Matrix I I K) * Matrix.diagonal D =
      Matrix.diagonal (D ∘ σ) * (W : Matrix I I K) := by
    rw [hW]
    exact monomial_mul_diagonal σ d D
  calc
    _ = (Matrix.diagonal (D ∘ σ) * (W : Matrix I I K)) *
        (↑(W⁻¹) : Matrix I I K) := congrArg (fun X => X * (↑(W⁻¹) : Matrix I I K)) hm
    _ = _ := by
      rw [mul_assoc, show (W : Matrix I I K) * (↑(W⁻¹) : Matrix I I K) = 1 from W.val_inv,
        mul_one]

/-- The original subgroup retains the full conjugated root group;
nonzero row weights are accounted for by the chosen preimage parameter. -/
theorem full_root_transfer (H : Subgroup ((Matrix I I K)ˣ))
    (W : (Matrix I I K)ˣ) (hHW : W ∈ H) (σ : Equiv.Perm I) (d : I → K)
    (hW : (W : Matrix I I K) = monomial σ d) (hd : ∀ k, d k ≠ 0)
    {i j : I} (hij : i ≠ j)
    (hRoot : ∀ a : K, transvectionUnit i j hij a ∈ H) :
    ∀ b : K, transvectionUnit (σ.symm i) (σ.symm j) (σ.symm.injective.ne hij) b ∈ H := by
  intro b
  let a := d (σ.symm j) * b / d (σ.symm i)
  have hm := H.mul_mem (H.mul_mem hHW (hRoot a)) (H.inv_mem hHW)
  rw [monomial_conjugation W σ d hW hij a (hd _)] at hm
  have he : d (σ.symm i) * a / d (σ.symm j) = b := by
    dsimp [a]
    field_simp [hd (σ.symm i), hd (σ.symm j)]
  simpa only [he] using hm

end SymmetricSubgroupAsymptotics.CFSGMonomialUnitRootAction
