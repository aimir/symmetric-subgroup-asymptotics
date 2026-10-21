import SymmetricSubgroupAsymptotics.CFSGMonomialUnitRootAction
import Mathlib.Tactic.Group

/-! A full root line can be propagated by A*W even when W itself is
not yet in the generating subgroup. The actual factor A must commute
with the output root line. This retains the original subgroup. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedMonomialRootTransport
open CFSGTypeAMonomialMatrices CFSGMonomialUnitRootAction
variable {I : Type*} [Fintype I] [DecidableEq I] {K : Type*} [Field K]

theorem commute_transvection_of_zero_products (A : (Matrix I I K)ˣ)
    (X : Matrix I I K) (a : K) (hA : (A : Matrix I I K) = 1 + a • X)
    (i j : I) (hij : i ≠ j)
    (hleft : X * Matrix.single i j 1 = 0)
    (hright : Matrix.single i j 1 * X = 0) (b : K) :
    Commute A (transvectionUnit i j hij b) := by
  change A * transvectionUnit i j hij b = transvectionUnit i j hij b * A
  apply Units.ext
  change (A : Matrix I I K) * Matrix.transvection i j b =
    Matrix.transvection i j b * (A : Matrix I I K)
  have ht : Matrix.transvection i j b = 1 + b • Matrix.single i j (1 : K) := by
    simp only [Matrix.transvection, Matrix.smul_single, smul_eq_mul, mul_one]
  rw [hA, ht]
  simp only [Matrix.mul_add, Matrix.add_mul, mul_one, one_mul, Matrix.mul_smul,
    Matrix.smul_mul, smul_smul, hleft, hright, smul_zero, add_zero]
  abel

theorem full_root_transfer (H : Subgroup ((Matrix I I K)ˣ))
    (A W : (Matrix I I K)ˣ) (hAW : A * W ∈ H) (σ : Equiv.Perm I) (d : I → K)
    (hW : (W : Matrix I I K) = monomial σ d) (hd : ∀ i, d i ≠ 0)
    {i j : I} (hij : i ≠ j)
    (hRoot : ∀ a : K, transvectionUnit i j hij a ∈ H)
    (hComm : ∀ b : K, Commute A
      (transvectionUnit (σ.symm i) (σ.symm j) (σ.symm.injective.ne hij) b)) :
    ∀ b : K, transvectionUnit (σ.symm i) (σ.symm j) (σ.symm.injective.ne hij) b ∈ H := by
  intro b
  let a := d (σ.symm j) * b / d (σ.symm i)
  have hm := H.mul_mem (H.mul_mem hAW (hRoot a)) (H.inv_mem hAW)
  have he : d (σ.symm i) * a / d (σ.symm j) = b := by
    dsimp [a]
    field_simp [hd (σ.symm i), hd (σ.symm j)]
  have hw : W * transvectionUnit i j hij a * W⁻¹ =
      transvectionUnit (σ.symm i) (σ.symm j) (σ.symm.injective.ne hij) b := by
    rw [CFSGMonomialUnitRootAction.monomial_conjugation W σ d hW hij a (hd _), he]
  have hc : (A * W) * transvectionUnit i j hij a * (A * W)⁻¹ =
      transvectionUnit (σ.symm i) (σ.symm j) (σ.symm.injective.ne hij) b := by
    calc
      _ = A * (W * transvectionUnit i j hij a * W⁻¹) * A⁻¹ := by group
      _ = A * transvectionUnit (σ.symm i) (σ.symm j) (σ.symm.injective.ne hij) b * A⁻¹ := by rw [hw]
      _ = _ := by rw [(hComm b).eq]; group
  rwa [hc] at hm

end SymmetricSubgroupAsymptotics.CFSGTwistedMonomialRootTransport
