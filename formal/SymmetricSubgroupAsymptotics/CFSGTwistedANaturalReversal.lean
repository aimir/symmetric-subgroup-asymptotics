import SymmetricSubgroupAsymptotics.CFSGTwistedANaturalMatrixInvolution
import SymmetricSubgroupAsymptotics.CFSGTwistedANaturalCartan
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationMonomialAction

/-! Exact reversed-generator formulas for the signed anti-diagonal Lie
map. The imported monomial lemma is generic on matrix units; no D group
recognition or source hypothesis is used. -/

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedANaturalMatrices
variable (K : Type) [Field K] (r : ℕ)

theorem signedReversalUnit_monomial :
    (signedReversalUnit K r : Mat K r) =
      CFSGTypeAMonomialMatrices.monomial Fin.revPerm (signWeight K r) := rfl

theorem signWeight_ne_zero (j : Fin (r + 1)) : signWeight K r j ≠ 0 :=
  pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)

theorem signWeight_cast_succ_ratio (i : Fin r) :
    signWeight K r i.castSucc / signWeight K r i.succ = -1 := by
  change (-1 : K) ^ i.val / (-1 : K) ^ (i.val + 1) = -1
  have hz : (-1 : K) ^ i.val ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  rw [pow_succ]
  field_simp [hz] <;> ring

theorem signWeight_succ_cast_ratio (i : Fin r) :
    signWeight K r i.succ / signWeight K r i.castSucc = -1 := by
  change (-1 : K) ^ (i.val + 1) / (-1 : K) ^ i.val = -1
  have hz : (-1 : K) ^ i.val ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  rw [pow_succ]
  field_simp [hz] <;> ring

theorem matrixDiagram_positive (i : Fin r) :
    matrixDiagram K r (positive K r i) = positive K r i.rev := by
  let J := signedReversalUnit K r
  have hc := CFSGOrthogonalDGenerationMonomialAction.conjugation_single
    J Fin.revPerm (signWeight K r) (signedReversalUnit_monomial K r)
    i.succ i.castSucc 1 (signWeight_ne_zero K r _)
  simp only [Fin.revPerm_symm, Fin.revPerm_apply, Fin.rev_succ, Fin.rev_castSucc,
    mul_one, signWeight_cast_succ_ratio] at hc
  change (J : Mat K r) * (-(positive K r i).transpose) *
    (↑(J⁻¹) : Mat K r) = positive K r i.rev
  simp only [positive, Matrix.transpose_single, mul_neg, neg_mul]
  rw [hc]
  ext a b
  simp only [Matrix.neg_apply, Matrix.single, Matrix.of_apply]
  split_ifs <;> simp

theorem matrixDiagram_negative (i : Fin r) :
    matrixDiagram K r (negative K r i) = negative K r i.rev := by
  let J := signedReversalUnit K r
  have hc := CFSGOrthogonalDGenerationMonomialAction.conjugation_single
    J Fin.revPerm (signWeight K r) (signedReversalUnit_monomial K r)
    i.castSucc i.succ 1 (signWeight_ne_zero K r _)
  simp only [Fin.revPerm_symm, Fin.revPerm_apply, Fin.rev_succ, Fin.rev_castSucc,
    mul_one, signWeight_succ_cast_ratio] at hc
  change (J : Mat K r) * (-(negative K r i).transpose) *
    (↑(J⁻¹) : Mat K r) = negative K r i.rev
  simp only [negative, Matrix.transpose_transpose, positive,
    Matrix.transpose_single, mul_neg, neg_mul]
  rw [hc]
  ext a b
  simp only [Matrix.neg_apply, Matrix.single, Matrix.of_apply]
  split_ifs <;> simp

theorem matrixDiagram_cartan (i : Fin r) :
    matrixDiagram K r (cartan K r i) = cartan K r i.rev := by
  change matrixDiagram K r ⁅positive K r i, negative K r i⁆ =
    ⁅positive K r i.rev, negative K r i.rev⁆
  rw [LieHom.map_lie, matrixDiagram_positive, matrixDiagram_negative]

end SymmetricSubgroupAsymptotics.CFSGTwistedANaturalMatrices
