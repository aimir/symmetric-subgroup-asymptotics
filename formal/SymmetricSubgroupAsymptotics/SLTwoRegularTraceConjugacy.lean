import SymmetricSubgroupAsymptotics.FiniteFieldBinaryNormSurjectivity
import SymmetricSubgroupAsymptotics.SLTwoConjugacyFibre
import SymmetricSubgroupAsymptotics.FiniteTwoTraceConjugacy
import Mathlib.Tactic.Group

/-! Away from trace squared equal to four, the ACTUAL GL2 centralizer
of an SL2 matrix has surjective determinant. A determinant-correcting
centralizer factor turns every actual GL2 conjugator into an SL2
conjugator. No split/nonsplit torus classification is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SLTwoRegularTraceConjugacy
variable {K : Type*} [Field K]

theorem linear_combination_det (A : Matrix (Fin 2) (Fin 2) K) (a b : K) :
    (a • (1 : Matrix (Fin 2) (Fin 2) K)+b • A).det=
      a^2+A.trace*a*b+A.det*b^2 := by
  simp [Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.add_apply,
    Matrix.smul_apply, Pi.smul_apply, smul_eq_mul, Matrix.one_apply]
  ring

theorem commute_linear_combination (A : Matrix (Fin 2) (Fin 2) K) (a b : K) :
    A*(a • (1 : Matrix (Fin 2) (Fin 2) K)+b • A)=
      (a • (1 : Matrix (Fin 2) (Fin 2) K)+b • A)*A := by
  simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_one, one_mul]

theorem centralizer_determinant_surjective [Finite K]
    (A : Matrix.SpecialLinearGroup (Fin 2) K) (ht : A.val.trace^2≠4) :
    ∀ δ : Kˣ, ∃ z : Matrix.GeneralLinearGroup (Fin 2) K,
      z ∈ Subgroup.centralizer ({Matrix.SpecialLinearGroup.toGL A} : Set _) ∧
      Matrix.GeneralLinearGroup.det z=δ := by
  intro δ
  obtain ⟨a,b,hab⟩ := FiniteFieldBinaryNormSurjectivity.exists_norm A.val.trace (δ:K) ht
  have hd : (a • (1 : Matrix (Fin 2) (Fin 2) K)+b • A.val).det=(δ:K) := by
    rw [linear_combination_det, A.property, one_mul]
    exact hab
  let z := Matrix.GeneralLinearGroup.mkOfDetNeZero
    (a • (1 : Matrix (Fin 2) (Fin 2) K)+b • A.val) (by rw [hd]; exact δ.ne_zero)
  refine ⟨z, ?_, ?_⟩
  · apply Subgroup.mem_centralizer_iff.mpr
    intro y hy
    have he : y=Matrix.SpecialLinearGroup.toGL A := Set.mem_singleton_iff.mp hy
    subst y
    apply Units.ext
    change A.val*(a • (1 : Matrix (Fin 2) (Fin 2) K)+b • A.val)=
      (a • (1 : Matrix (Fin 2) (Fin 2) K)+b • A.val)*A.val
    exact commute_linear_combination A.val a b
  · apply Units.ext
    exact hd

theorem isConj_of_toGL_isConj [Finite K]
    (A B : Matrix.SpecialLinearGroup (Fin 2) K) (ht : A.val.trace^2≠4)
    (hc : IsConj (Matrix.SpecialLinearGroup.toGL A) (Matrix.SpecialLinearGroup.toGL B)) :
    IsConj A B := by
  obtain ⟨g,hg⟩ := isConj_iff.mp hc
  obtain ⟨z,hz,hdet⟩ := centralizer_determinant_surjective A ht
    (Matrix.GeneralLinearGroup.det g)⁻¹
  have hzcomm : Matrix.SpecialLinearGroup.toGL A*z=z*Matrix.SpecialLinearGroup.toGL A :=
    (Subgroup.mem_centralizer_iff.mp hz) _ rfl
  have hzconj : z*Matrix.SpecialLinearGroup.toGL A*z⁻¹=Matrix.SpecialLinearGroup.toGL A := by
    rw [← hzcomm, mul_assoc, mul_inv_cancel, mul_one]
  let p : SLTwoConjugacyFibre.specialLinearKernel K := ⟨g*z, by
    change Matrix.GeneralLinearGroup.det (g*z)=1
    rw [map_mul, hdet, mul_inv_cancel]⟩
  let E := SLTwoConjugacyFibre.specialLinearKernelEquiv K
  let h := E.symm p
  have hh : Matrix.SpecialLinearGroup.toGL h=g*z := by
    have he := congrArg (fun q : SLTwoConjugacyFibre.specialLinearKernel K => q.val)
      (E.apply_symm_apply p)
    change (SLTwoConjugacyFibre.specialLinearKernelEquiv K h).val=g*z at he
    rw [SLTwoConjugacyFibre.specialLinearKernelEquiv_val] at he
    exact he
  apply isConj_iff.mpr
  refine ⟨h, ?_⟩
  apply Matrix.SpecialLinearGroup.toGL_injective
  rw [map_mul, map_mul, map_inv, hh]
  calc
    (g*z)*Matrix.SpecialLinearGroup.toGL A*(g*z)⁻¹=
        g*(z*Matrix.SpecialLinearGroup.toGL A*z⁻¹)*g⁻¹ := by group
    _ =Matrix.SpecialLinearGroup.toGL B := by rw [hzconj]; exact hg

theorem isConj_of_trace_eq [Finite K]
    (A B : Matrix.SpecialLinearGroup (Fin 2) K)
    (hA : A.val ∉ Set.range (Matrix.scalar (Fin 2)))
    (hB : B.val ∉ Set.range (Matrix.scalar (Fin 2)))
    (ht : A.val.trace^2≠4) (he : A.val.trace=B.val.trace) : IsConj A B :=
  isConj_of_toGL_isConj A B ht (FiniteTwoTraceConjugacy.isConj_toGL_of_trace_eq A B hA hB he)

end SymmetricSubgroupAsymptotics.SLTwoRegularTraceConjugacy
