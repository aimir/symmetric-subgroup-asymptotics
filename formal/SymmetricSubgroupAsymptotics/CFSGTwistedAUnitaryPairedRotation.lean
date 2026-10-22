import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryEndpointPair
import SymmetricSubgroupAsymptotics.CFSGMatrixPairRotationAction

/-! The actual defining-fixed paired Weyl word is the literal product of
two disjoint coordinate rotations. This retains signs in every field,
including characteristic2, and prepares nested-radical support transport. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent
open CFSGMatrixPairRotation CFSGSerreOrdinaryTwists

theorem double_pair_rotation_word {K I : Type*} [CommRing K] [Fintype I] [DecidableEq I]
    (p q r t : I) (hpq : p ≠ q) (hpr : p ≠ r) (hpt : p ≠ t)
    (hqr : q ≠ r) (hqt : q ≠ t) (hrt : r ≠ t) :
    ((1 : Matrix I I K) - Matrix.single p q 1 - Matrix.single r t 1) *
      (1 + Matrix.single q p 1 + Matrix.single t r 1) *
      (1 - Matrix.single p q 1 - Matrix.single r t 1) = rotation K p q * rotation K r t := by
  simp [rotation, sub_mul, mul_sub, add_mul, mul_add, hpr, hpt, hqr, hqt,
    Ne.symm hpq, Ne.symm hpr, Ne.symm hpt, Ne.symm hqt, Ne.symm hrt]
  abel

theorem endpointNaturalFixedPair_matrix (q : CFSG.PrimePower) (s : ℕ) (neg : Bool) (t : q.Extension 2) :
    ((endpointNaturalFixedPair q s neg t).val.val : Mat (q.Extension 2) (s + 3)) =
      1 + t • rootMatrix (q.Extension 2) (s + 3) neg (endpointNode s) +
        definingFieldAutomorphism q 2 t • rootMatrix (q.Extension 2) (s + 3) neg (endpointNode s).rev := by
  have hp := (endpoint_rootMatrix_mul_zero (q.Extension 2) s neg).1
  change (1 + t • rootMatrix (q.Extension 2) (s + 3) neg (endpointNode s)) *
    (1 + definingFieldAutomorphism q 2 t • rootMatrix (q.Extension 2) (s + 3) neg (endpointNode s).rev) = _
  simp only [mul_add, add_mul, one_mul, mul_one, smul_mul_assoc, mul_smul_comm,
    hp, smul_zero]
  abel

theorem endpointPairWeyl_matrix (q : CFSG.PrimePower) (s : ℕ) :
    ((endpointPairWeyl q s).val.val : Mat (q.Extension 2) (s + 3)) =
      rotation (q.Extension 2) (endpointNode s).castSucc (endpointNode s).succ *
        rotation (q.Extension 2) (endpointNode s).rev.castSucc (endpointNode s).rev.succ := by
  have hp : ((endpointNaturalFixedPair q s false (-1)).val.val : Mat (q.Extension 2) (s + 3)) =
      1 - Matrix.single (endpointNode s).castSucc (endpointNode s).succ 1 -
        Matrix.single (endpointNode s).rev.castSucc (endpointNode s).rev.succ 1 := by
    rw [endpointNaturalFixedPair_matrix]
    simp only [map_neg, map_one, rootMatrix, positive, neg_smul, one_smul, sub_eq_add_neg, Bool.false_eq_true, if_false, if_true]
  have hn : ((endpointNaturalFixedPair q s true 1).val.val : Mat (q.Extension 2) (s + 3)) =
      1 + Matrix.single (endpointNode s).succ (endpointNode s).castSucc 1 +
        Matrix.single (endpointNode s).rev.succ (endpointNode s).rev.castSucc 1 := by
    rw [endpointNaturalFixedPair_matrix]
    simp only [map_one, rootMatrix, negative, positive, Matrix.transpose_single, one_smul, if_true]
  change ((endpointNaturalFixedPair q s false (-1)).val.val : Mat (q.Extension 2) (s + 3)) *
    ((endpointNaturalFixedPair q s true 1).val.val : Mat (q.Extension 2) (s + 3)) *
      ((endpointNaturalFixedPair q s false (-1)).val.val : Mat (q.Extension 2) (s + 3)) = _
  rw [hp, hn]
  apply double_pair_rotation_word
  all_goals intro he
  all_goals have hv := congrArg (fun i : Fin (s + 4) => i.val) he
  all_goals simp only [endpointNode, Fin.val_castSucc, Fin.val_succ, Fin.val_rev] at hv
  all_goals omega

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
