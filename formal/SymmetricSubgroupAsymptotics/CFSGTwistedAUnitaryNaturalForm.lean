import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryRadical
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitIsometry
import Mathlib.LinearAlgebra.Matrix.Reindex

/-! Actual signed-form and coordinate transport for the natural radical.
The middle form is literally minus the existing signed reversal. The
isometry equation is transported through a displayed index equivalence,
then converted to the original defining fixed-unit equation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUnitaryUpperArrays

theorem signedMiddle_hermitian (R : Type*) [CommRing R] (f : R →+* R) (s : ℕ) :
    (-(signedReversalUnit R s : Mat R s)).map f =
      ((-1 : R) ^ s) • (-(signedReversalUnit R s : Mat R s)).transpose := by
  have hm : (-(signedReversalUnit R s : Mat R s)).map f =
      -(signedReversalUnit R s : Mat R s) := by
    change f.mapMatrix (-(signedReversalUnit R s : Mat R s)) = _
    rw [map_neg, map_signedReversalUnit_val]
  have he2 : ((-1 : R) ^ s) * ((-1 : R) ^ s) = 1 := by
    rw [← mul_pow]
    simp
  rw [hm, Matrix.transpose_neg, signedReversalUnit_transpose, smul_neg, smul_smul, he2,
    one_smul]

theorem blockForm_reindex (R : Type*) [CommRing R] (s : ℕ) :
    Matrix.reindex (splitEquiv s) (splitEquiv s)
      (blockForm ((-1 : R) ^ s) (-(signedReversalUnit R s : Mat R s))) =
        (signedReversalUnit R (s + 2) : Mat R (s + 2)) := by
  ext i j
  obtain ⟨x, rfl⟩ := (splitEquiv s).surjective i
  obtain ⟨y, rfl⟩ := (splitEquiv s).surjective j
  have h := congrArg (fun M : Matrix (Index (Fin (s + 1))) (Index (Fin (s + 1))) R => M x y)
    (signedForm_split R s)
  change (signedReversalUnit R (s + 2) : Mat R (s + 2))
    (splitEquiv s x) (splitEquiv s y) = _ at h
  simpa only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply] using h.symm

theorem reindex_map {K I J : Type*} [Field K] [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (e : I ≃ J) (f : K →+* K) (M : Matrix I I K) :
    Matrix.reindex e e (M.map f) = (Matrix.reindex e e M).map f := by
  ext i j
  rfl

theorem reindex_mul {K I J : Type*} [Field K] [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (e : I ≃ J) (A B : Matrix I I K) :
    Matrix.reindex e e (A * B) = Matrix.reindex e e A * Matrix.reindex e e B :=
  (Matrix.reindexAlgEquiv K K e).map_mul A B

theorem reindex_isometry {K I J : Type*} [Field K] [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (e : I ≃ J) (f : K →+* K) (H U : Matrix I I K)
    (h : (U.map f).transpose * H * U = H) :
    ((Matrix.reindex e e U).map f).transpose * Matrix.reindex e e H *
      Matrix.reindex e e U = Matrix.reindex e e H := by
  calc
    _ = Matrix.reindex e e ((U.map f).transpose) * Matrix.reindex e e H *
        Matrix.reindex e e U := by rw [← reindex_map, Matrix.transpose_reindex]
    _ = Matrix.reindex e e ((U.map f).transpose * H * U) := by
      rw [← reindex_mul, ← reindex_mul]
    _ = Matrix.reindex e e H := congrArg (Matrix.reindex e e) h

theorem unit_fixed_of_signedForm (K : Type) [Field K] (r : ℕ) (f : K →+* K)
    (u : (Mat K r)ˣ)
    (h : (f.mapMatrix (u : Mat K r)).transpose * (signedReversalUnit K r : Mat K r) *
      (u : Mat K r) = (signedReversalUnit K r : Mat K r)) :
    diagramFieldUnitHom K r f u = u := by
  apply unit_fixed_of_isometric K r f u
  rw [signedReversalUnit_inv_parity]
  calc
    _ = ((-1 : K) ^ r) • ((f.mapMatrix (u : Mat K r)).transpose *
        (signedReversalUnit K r : Mat K r) * (u : Mat K r)) := by
      simp only [mul_smul_comm, smul_mul_assoc]
    _ = _ := congrArg (fun M : Mat K r => ((-1 : K) ^ r) • M) h

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
