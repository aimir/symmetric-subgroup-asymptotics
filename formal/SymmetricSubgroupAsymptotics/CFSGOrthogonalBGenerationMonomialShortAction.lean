import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationShortArrays
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationMonomialAction

/-! Exact short-root transport by an actual monomial unit. The two
linear weights and the quadratic coefficient are checked together; this
does not replace a quadratic short root by a square-zero transvection. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationMonomialShortAction
open Matrix CFSGOrthogonalBSerreMatrices CFSGOrthogonalBGenerationShortArrays
open CFSGOrthogonalDGenerationMonomialAction CFSGTypeAMonomialMatrices
variable {K : Type} [Field K] {r : ℕ}

theorem shortUnit_sparse (b : Fin r ⊕ Fin r) (a : K) :
    (shortUnit K r b a : Mat K r) =
      1 + Matrix.single (Sum.inl b) (middle r) a -
        Matrix.single (middle r) (Sum.inl (paired r b)) (2 * a) -
        Matrix.single (Sum.inl b) (Sum.inl (paired r b)) (a ^ 2) := by
  rw [shortUnit_val]
  ext i j
  simp [shortArray, shortSecond, Matrix.single]
  all_goals try split_ifs
  all_goals ring

theorem short_conjugation (W : (Mat K r)ˣ) (σ : Equiv.Perm (Index r))
    (d : Index r → K) (hW : (W : Mat K r) = monomial σ d)
    (b c : Fin r ⊕ Fin r) (l a : K)
    (hm : σ.symm (middle r) = middle r)
    (hb : σ.symm (Sum.inl b) = Sum.inl c)
    (hp : σ.symm (Sum.inl (paired r b)) = Sum.inl (paired r c))
    (hdm : d (middle r) ≠ 0) (hdp : d (σ.symm (Sum.inl (paired r b))) ≠ 0)
    (hl : d (σ.symm (Sum.inl b)) = l * d (middle r))
    (hr : d (middle r) = l * d (σ.symm (Sum.inl (paired r b)))) :
    W * shortUnit K r b a * W⁻¹ = shortUnit K r c (l * a) := by
  have hdm' : d (σ.symm (middle r)) ≠ 0 := by simpa only [hm] using hdm
  have hleft (x : K) : d (σ.symm (Sum.inl b)) * x / d (σ.symm (middle r)) = l * x := by
    rw [hm, hl]
    field_simp [hdm]
    all_goals ring
  have hright (x : K) : d (σ.symm (middle r)) * x /
      d (σ.symm (Sum.inl (paired r b))) = l * x := by
    rw [hm, hr]
    field_simp [hdp]
    all_goals ring
  have hdiag (x : K) : d (σ.symm (Sum.inl b)) * x /
      d (σ.symm (Sum.inl (paired r b))) = l ^ 2 * x := by
    rw [hl, hr]
    field_simp [hdp]
    all_goals ring
  apply Units.ext
  change (W : Mat K r) * (shortUnit K r b a : Mat K r) * (↑W⁻¹ : Mat K r) = _
  rw [shortUnit_sparse, shortUnit_sparse]
  simp only [mul_sub, sub_mul, mul_add, add_mul, mul_one, Units.mul_inv,
    conjugation_single W σ d hW (Sum.inl b) (middle r) a hdm',
    conjugation_single W σ d hW (middle r) (Sum.inl (paired r b)) (2 * a) hdp,
    conjugation_single W σ d hW (Sum.inl b) (Sum.inl (paired r b)) (a ^ 2) hdp]
  rw [hleft a, hright (2 * a), hdiag (a ^ 2), hm, hb, hp]
  ext i j
  simp [Matrix.single]
  all_goals try split_ifs
  all_goals ring

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationMonomialShortAction
