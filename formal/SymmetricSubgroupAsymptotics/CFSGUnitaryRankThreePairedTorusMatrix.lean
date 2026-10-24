import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryPairedTorus
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FieldSimp

/-! Exact four-coordinate matrices of the actual endpoint-paired Weyl
and torus words. The paired torus is not replaced by a full unitary
Levi, and all extension-field scalars are retained. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent CFSGSerreOrdinaryTwists

private theorem rankThree_endpointPair_matrix (q : CFSG.PrimePower)
    (neg : Bool) (a : q.Extension 2) :
    ((endpointNaturalFixedPair q 0 neg a).val.val : Mat (q.Extension 2) 3) =
      if neg then
        !![1,0,0,0; a,1,0,0; 0,0,1,0; 0,0,definingFieldAutomorphism q 2 a,1]
      else
        !![1,a,0,0; 0,1,0,0; 0,0,1,definingFieldAutomorphism q 2 a; 0,0,0,1] := by
  rw [endpointNaturalFixedPair_matrix]
  cases neg <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [rootMatrix, positive, negative, endpointNode, Fin.rev,
      Matrix.add_apply, Matrix.smul_apply, Matrix.transpose_apply, Matrix.one_apply,
      Matrix.single_apply, Fin.ext_iff]

theorem rankThree_pairedWeylParameter_matrix (q : CFSG.PrimePower)
    (a : q.Extension 2) (ha : a ≠ 0) :
    ((pairedWeylParameter q 0 a).val.val : Mat (q.Extension 2) 3) =
      !![0,a,0,0; -a⁻¹,0,0,0;
        0,0,0,definingFieldAutomorphism q 2 a;
        0,0,-(definingFieldAutomorphism q 2 a)⁻¹,0] := by
  change (((endpointNaturalFixedPair q 0 false a).val.val : Mat (q.Extension 2) 3) *
    ((endpointNaturalFixedPair q 0 true (-a⁻¹)).val.val : Mat (q.Extension 2) 3)) *
      ((endpointNaturalFixedPair q 0 false a).val.val : Mat (q.Extension 2) 3) = _
  simp only [rankThree_endpointPair_matrix]
  have hs : definingFieldAutomorphism q 2 a ≠ 0 :=
    (map_ne_zero (definingFieldAutomorphism q 2)).mpr ha
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, map_neg, map_inv₀,
      Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail] <;>
    field_simp [ha, hs] <;> simp <;> ring

theorem rankThree_pairedTorus_matrix (q : CFSG.PrimePower)
    (a : q.Extension 2) (ha : a ≠ 0) :
    ((pairedTorus q 0 a).val.val : Mat (q.Extension 2) 3) =
      Matrix.diagonal ![a,a⁻¹,definingFieldAutomorphism q 2 a,
        (definingFieldAutomorphism q 2 a)⁻¹] := by
  change ((pairedWeylParameter q 0 a).val.val : Mat (q.Extension 2) 3) *
    ((pairedWeylParameter q 0 (-1)).val.val : Mat (q.Extension 2) 3) = _
  rw [rankThree_pairedWeylParameter_matrix q a ha,
    rankThree_pairedWeylParameter_matrix q (-1) (neg_ne_zero.mpr one_ne_zero)]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.diagonal, Fin.sum_univ_succ,
      Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
