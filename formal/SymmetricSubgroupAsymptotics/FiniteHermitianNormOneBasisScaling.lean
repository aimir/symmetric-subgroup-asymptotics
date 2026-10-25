import SymmetricSubgroupAsymptotics.FiniteHermitianOrthonormalCoordinates
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.LinearAlgebra.Determinant

/-! A prescribed norm-one unit occurs as the determinant of an actual
Hermitian isometry: scale ONE orthonormal basis vector and fix the rest.
This constructs the determinant witness and assumes no order formula. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.FiniteHermitianNormOneBasisScaling
open Module CFSGTwistedAUnitaryParameters
open FiniteHermitianBasisCoordinates FiniteHermitianOrthonormalCoordinates

theorem exists_isometry_determinant {K I : Type*} [Field K] [Fintype I]
    (sigma : K ≃+* K) (H : Matrix I I K)
    {n : ℕ} (b : Basis (Fin n) K (I → K))
    (hb : ∀ i j, hermitianPair sigma H (b i) (b j)=if i=j then 1 else 0)
    (i₀ : Fin n) (z : Kˣ) (hz : sigma (z : K)*(z : K)=1) :
    ∃ e : (I → K) ≃ₗ[K] (I → K),
      (∀ x y, hermitianPair sigma H (e x) (e y)=hermitianPair sigma H x y) ∧
      LinearMap.det e.toLinearMap=(z : K) := by
  classical
  let d : Fin n → Kˣ := fun i => if i=i₀ then z else 1
  let b' := b.unitsSMul d
  let e := b.equiv b' (Equiv.refl (Fin n))
  have hd (i : Fin n) : sigma (d i : K)*(d i : K)=1 := by
    by_cases hi : i=i₀
    · simpa only [d,if_pos hi] using hz
    · simp only [d,if_neg hi,Units.val_one,map_one,mul_one]
  have hb' : ∀ i j, hermitianPair sigma H (b' i) (b' j)=if i=j then 1 else 0 := by
    intro i j
    change hermitianPair sigma H ((b.unitsSMul d) i) ((b.unitsSMul d) j)=_
    rw [Basis.unitsSMul_apply,Basis.unitsSMul_apply]
    simp only [Units.smul_def,hermitianPair_smul,hb]
    by_cases hij : i=j
    · subst j
      rw [if_pos rfl,mul_one,hd]
    · rw [if_neg hij,mul_zero]
  have he (x : I → K) : b'.repr (e x)=b.repr x := by
    simp only [e,Basis.equiv,Equiv.refl_symm,Basis.reindex_refl,
      LinearEquiv.trans_apply,LinearEquiv.apply_symm_apply]
  refine ⟨e,?_,?_⟩
  · intro x y
    calc
      _ = coordinatePair sigma b' (e x) (e y) :=
        pairing_eq_coordinatePair sigma H b' hb' (e x) (e y)
      _ = coordinatePair sigma b x y := by
        unfold coordinatePair
        rw [he,he]
      _ = _ := (pairing_eq_coordinatePair sigma H b hb x y).symm
  · change LinearMap.det (b.equiv (b.unitsSMul d) (Equiv.refl (Fin n))).toLinearMap=(z : K)
    rw [Basis.det_basis,Basis.det_unitsSMul_self]
    change (∏ i : Fin n, (d i : K))=(z : K)
    rw [Finset.prod_eq_single i₀]
    · simp [d]
    · intro j _ hj
      simp [d,hj]
    · intro hi
      exact (hi (Finset.mem_univ i₀)).elim

end SymmetricSubgroupAsymptotics.FiniteHermitianNormOneBasisScaling
