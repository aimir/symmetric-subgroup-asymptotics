import SymmetricSubgroupAsymptotics.FiniteTwoCyclicColumns
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Algebra.Group.Conj

/-! A nonscalar two-by-two matrix is conjugate over the actual general
linear group to its trace/determinant companion. Consequently two
nonscalar determinant-one matrices of the same trace are GL2-conjugate,
over every field including characteristic two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FiniteTwoTraceConjugacy
open FiniteTwoCyclicColumns
variable {K : Type*} [Field K]

theorem exists_companion_conjugator (A : Matrix (Fin 2) (Fin 2) K)
    (hA : A ∉ Set.range (Matrix.scalar (Fin 2))) :
    ∃ P : Matrix.GeneralLinearGroup (Fin 2) K,
      (↑(P⁻¹) : Matrix (Fin 2) (Fin 2) K) * A * (P : Matrix (Fin 2) (Fin 2) K) =
        companion A.trace A.det := by
  obtain ⟨v,hv⟩ := exists_cyclic_columns A hA
  let P := Matrix.GeneralLinearGroup.mkOfDetNeZero (cyclicColumns A v) hv
  have hP : (P : Matrix (Fin 2) (Fin 2) K)=cyclicColumns A v := rfl
  have hc : A*(P : Matrix (Fin 2) (Fin 2) K)=
      (P : Matrix (Fin 2) (Fin 2) K)*companion A.trace A.det := by
    rw [hP]
    exact mul_cyclic_columns A v
  refine ⟨P, ?_⟩
  calc
    (↑(P⁻¹) : Matrix (Fin 2) (Fin 2) K)*A*(P : Matrix (Fin 2) (Fin 2) K) =
        (↑(P⁻¹) : Matrix (Fin 2) (Fin 2) K)*(A*(P : Matrix (Fin 2) (Fin 2) K)) :=
      mul_assoc _ _ _
    _ =(↑(P⁻¹) : Matrix (Fin 2) (Fin 2) K)*
        ((P : Matrix (Fin 2) (Fin 2) K)*companion A.trace A.det) := by rw [hc]
    _ =companion A.trace A.det := by rw [← mul_assoc, Units.inv_mul, one_mul]

def specialCompanion (t : K) : Matrix.SpecialLinearGroup (Fin 2) K :=
  ⟨companion t 1, companion_det t 1⟩

theorem specialCompanion_val (t : K) :
    (specialCompanion t).val=companion t 1 := rfl

theorem exists_special_companion_conjugator (A : Matrix.SpecialLinearGroup (Fin 2) K)
    (hA : A.val ∉ Set.range (Matrix.scalar (Fin 2))) :
    ∃ P : Matrix.GeneralLinearGroup (Fin 2) K,
      (↑(P⁻¹) : Matrix (Fin 2) (Fin 2) K) * A.val * (P : Matrix (Fin 2) (Fin 2) K) =
        (specialCompanion A.val.trace).val := by
  obtain ⟨P,hP⟩ := exists_companion_conjugator A.val hA
  refine ⟨P, ?_⟩
  simpa only [A.property, specialCompanion_val] using hP

theorem isConj_toGL_of_trace_eq
    (A B : Matrix.SpecialLinearGroup (Fin 2) K)
    (hA : A.val ∉ Set.range (Matrix.scalar (Fin 2)))
    (hB : B.val ∉ Set.range (Matrix.scalar (Fin 2))) (ht : A.val.trace=B.val.trace) :
    IsConj (Matrix.SpecialLinearGroup.toGL A) (Matrix.SpecialLinearGroup.toGL B) := by
  have hC (X : Matrix.SpecialLinearGroup (Fin 2) K)
      (hX : X.val ∉ Set.range (Matrix.scalar (Fin 2))) :
      IsConj (Matrix.SpecialLinearGroup.toGL X)
        (Matrix.SpecialLinearGroup.toGL (specialCompanion X.val.trace)) := by
    obtain ⟨P,hP⟩ := exists_special_companion_conjugator X hX
    apply isConj_iff.mpr
    refine ⟨P⁻¹, ?_⟩
    apply Units.ext
    change (↑(P⁻¹) : Matrix (Fin 2) (Fin 2) K)*X.val*
      (↑((P⁻¹)⁻¹) : Matrix (Fin 2) (Fin 2) K)=(specialCompanion X.val.trace).val
    simpa only [inv_inv] using hP
  have hAC := hC A hA
  rw [ht] at hAC
  exact hAC.trans (hC B hB).symm

end SymmetricSubgroupAsymptotics.FiniteTwoTraceConjugacy
