import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD2ProjectiveLines

/-! A nonzero residual rank-one ray lies in exactly one column ruling
and one row ruling. Both parameters are recovered from actual linear
map ranges, rather than postulated incidence coordinates. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped LinearAlgebra.Projectivization
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD2Coordinates
variable (K : Type) [Field K]

theorem range_le_factor_of_column_mem (u : Fin 2 → K)
    (A : Matrix (Fin 2) (Fin 2) K) (hA : A ∈ columnPlane K u) :
    LinearMap.range (Matrix.mulVecLin A) ≤ Submodule.span K {u} := by
  obtain ⟨v, rfl⟩ := hA
  rintro z ⟨x, rfl⟩
  rw [Matrix.mulVecLin_apply, outer_mulVec]
  exact (Submodule.span K {u}).smul_mem _ (Submodule.mem_span_singleton_self _)

theorem range_transpose_le_factor_of_row_mem (u : Fin 2 → K)
    (A : Matrix (Fin 2) (Fin 2) K) (hA : A ∈ rowPlane K u) :
    LinearMap.range (Matrix.mulVecLin A.transpose) ≤ Submodule.span K {u} := by
  obtain ⟨v, rfl⟩ := hA
  have he : (rowMap K u v).transpose = columnMap K u v := by
    ext i j
    change v j * u i = u i * v j
    exact mul_comm _ _
  rw [he]
  exact range_le_factor_of_column_mem K u _ ⟨v, rfl⟩

theorem segreLine_le_columnPlane_iff (p q u : RulingParameters K) :
    (segreLine K (p, q)).val ≤ columnPlane K u.rep ↔ p = u := by
  constructor
  · intro h
    have hA : columnMap K p.rep q.rep ∈ columnPlane K u.rep :=
      h (Submodule.mem_span_singleton_self _)
    have hh := range_le_factor_of_column_mem K u.rep _ hA
    rw [outer_range K _ _ q.rep_nonzero] at hh
    have he : Submodule.span K {p.rep} = Submodule.span K {u.rep} :=
      Submodule.eq_of_le_of_finrank_le hh (by
        rw [finrank_span_singleton p.rep_nonzero, finrank_span_singleton u.rep_nonzero])
    apply Projectivization.submodule_injective
    simpa only [Projectivization.submodule_eq] using he
  · rintro rfl
    exact (Submodule.span_singleton_le_iff_mem _ _).mpr ⟨q.rep, rfl⟩

theorem segreLine_le_rowPlane_iff (p q v : RulingParameters K) :
    (segreLine K (p, q)).val ≤ rowPlane K v.rep ↔ q = v := by
  constructor
  · intro h
    have hA : columnMap K p.rep q.rep ∈ rowPlane K v.rep :=
      h (Submodule.mem_span_singleton_self _)
    have hh := range_transpose_le_factor_of_row_mem K v.rep _ hA
    rw [outer_transpose_range K _ _ p.rep_nonzero] at hh
    have he : Submodule.span K {q.rep} = Submodule.span K {v.rep} :=
      Submodule.eq_of_le_of_finrank_le hh (by
        rw [finrank_span_singleton q.rep_nonzero, finrank_span_singleton v.rep_nonzero])
    apply Projectivization.submodule_injective
    simpa only [Projectivization.submodule_eq] using he
  · rintro rfl
    apply (Submodule.span_singleton_le_iff_mem _ _).mpr
    refine ⟨p.rep, ?_⟩
    ext i j
    rfl

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD2Coordinates
