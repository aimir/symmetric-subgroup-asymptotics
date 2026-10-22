import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD2OuterRanges
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD2Rulings

/-! The two projective factors of a residual rank-one matrix are
intrinsically unique. Equality of the actual matrix rays forces equality
of both factors via actual range and transpose-range, not an order match. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix LinearAlgebra.Projectivization
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD2Coordinates
variable (K : Type) [Field K]

theorem scalar_matrix_range (A : Matrix (Fin 2) (Fin 2) K) (a : K) (ha : a ≠ 0) :
    LinearMap.range (Matrix.mulVecLin (a • A)) = LinearMap.range (Matrix.mulVecLin A) := by
  have he : Matrix.mulVecLin (a • A) = a • Matrix.mulVecLin A := by
    apply LinearMap.ext
    intro x
    exact Matrix.smul_mulVec a A x
  rw [he, LinearMap.range_smul _ a ha]

def segrePoint (p q : RulingParameters K) : ℙ K (Matrix (Fin 2) (Fin 2) K) :=
  Projectivization.mk K (columnMap K p.rep q.rep) (outer_nonzero K p.rep q.rep p.rep_nonzero q.rep_nonzero)

theorem segrePoint_pair_injective :
    Function.Injective (fun pq : RulingParameters K × RulingParameters K => segrePoint K pq.1 pq.2) := by
  rintro ⟨p, q⟩ ⟨p', q'⟩ he
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff K
    (columnMap K p'.rep q'.rep) (columnMap K p.rep q.rep)
    (outer_nonzero K p'.rep q'.rep p'.rep_nonzero q'.rep_nonzero)
    (outer_nonzero K p.rep q.rep p.rep_nonzero q.rep_nonzero)).mp he.symm
  have hcol := congrArg (fun A : Matrix (Fin 2) (Fin 2) K => LinearMap.range (Matrix.mulVecLin A)) ha
  change LinearMap.range (Matrix.mulVecLin ((a : K) • columnMap K p.rep q.rep)) =
    LinearMap.range (Matrix.mulVecLin (columnMap K p'.rep q'.rep)) at hcol
  rw [scalar_matrix_range K _ a a.ne_zero, outer_range K _ _ q.rep_nonzero,
    outer_range K _ _ q'.rep_nonzero] at hcol
  have hrow := congrArg (fun A : Matrix (Fin 2) (Fin 2) K =>
    LinearMap.range (Matrix.mulVecLin A.transpose)) ha
  change LinearMap.range (Matrix.mulVecLin (((a : K) • columnMap K p.rep q.rep).transpose)) =
    LinearMap.range (Matrix.mulVecLin (columnMap K p'.rep q'.rep).transpose) at hrow
  rw [Matrix.transpose_smul, scalar_matrix_range K _ a a.ne_zero,
    outer_transpose_range K _ _ p.rep_nonzero, outer_transpose_range K _ _ p'.rep_nonzero] at hrow
  apply Prod.ext
  · apply Projectivization.submodule_injective
    rw [Projectivization.submodule_eq, Projectivization.submodule_eq]
    exact hcol
  · apply Projectivization.submodule_injective
    rw [Projectivization.submodule_eq, Projectivization.submodule_eq]
    exact hrow

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD2Coordinates
