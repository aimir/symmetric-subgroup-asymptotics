import SymmetricSubgroupAsymptotics.CFSGTwistedANaturalDiagramScalars

/-! The exact signed anti-diagonal form in the original natural diagram.
Its transpose and inverse differ from itself by the INTEGER parity sign,
all ranks and coefficient characteristics. These identities keep the
unitary form binding literal rather than choosing a named form model. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics.CFSGTwistedANaturalMatrices
variable (R : Type*) [CommRing R] (r : ℕ)

theorem signWeight_mul_rev (i : Fin (r + 1)) :
    signWeight R r i * signWeight R r i.rev = (-1 : R) ^ r := by
  change (-1 : R) ^ i.val * (-1 : R) ^ i.rev.val = _
  rw [← pow_add, i.add_rev_cast]

theorem signWeight_rev (i : Fin (r + 1)) :
    signWeight R r i.rev = (-1 : R) ^ r * signWeight R r i := by
  calc
    _ = 1 * signWeight R r i.rev := (one_mul _).symm
    _ = (signWeight R r i * signWeight R r i) * signWeight R r i.rev := by
      rw [signWeight_square]
    _ = signWeight R r i * (signWeight R r i * signWeight R r i.rev) := mul_assoc _ _ _
    _ = signWeight R r i * (-1 : R) ^ r := by rw [signWeight_mul_rev]
    _ = (-1 : R) ^ r * signWeight R r i := mul_comm _ _

theorem signedReversalUnit_transpose :
    (signedReversalUnit R r : Mat R r).transpose =
      ((-1 : R) ^ r) • (signedReversalUnit R r : Mat R r) := by
  ext i j
  simp only [Matrix.transpose_apply, signedReversalUnit_apply, Matrix.smul_apply,
    smul_eq_mul]
  by_cases h : i.rev = j
  · subst j
    simp only [Fin.rev_rev, if_true, signWeight_rev]
  · have h' : j.rev ≠ i := by
      intro hh
      apply h
      have he := congrArg Fin.rev hh
      simpa only [Fin.rev_rev] using he.symm
    simp only [if_neg h, if_neg h', mul_zero]

theorem signedReversalUnit_orthogonal :
    (signedReversalUnit R r : Mat R r).transpose * (signedReversalUnit R r : Mat R r) = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  have hentry (k : Fin (r + 1)) :
      (signedReversalUnit R r : Mat R r).transpose i k *
        (signedReversalUnit R r : Mat R r) k j =
        if k = i.rev then (if i = j then 1 else 0) else 0 := by
    simp only [Matrix.transpose_apply, signedReversalUnit_apply]
    by_cases hk : k = i.rev
    · subst k
      simp only [Fin.rev_rev, if_true]
      by_cases hij : i = j
      · simp only [hij, if_true, signWeight_square]
      · simp only [if_neg hij, mul_zero]
    · have hki : k.rev ≠ i := by
        intro hh
        apply hk
        simpa only [Fin.rev_rev] using congrArg Fin.rev hh
      simp only [if_neg hki, zero_mul, if_neg hk]
  simp only [hentry, Finset.sum_ite_eq', Finset.mem_univ, if_true, Matrix.one_apply]

theorem signedReversalUnit_inv_eq_transpose :
    (↑((signedReversalUnit R r)⁻¹) : Mat R r) =
      (signedReversalUnit R r : Mat R r).transpose := by
  calc
    _ = 1 * (↑((signedReversalUnit R r)⁻¹) : Mat R r) := (one_mul _).symm
    _ = ((signedReversalUnit R r : Mat R r).transpose * (signedReversalUnit R r : Mat R r)) *
        (↑((signedReversalUnit R r)⁻¹) : Mat R r) := by rw [signedReversalUnit_orthogonal]
    _ = (signedReversalUnit R r : Mat R r).transpose := by
      rw [mul_assoc, Units.mul_inv, mul_one]

theorem signedReversalUnit_inv_parity :
    (↑((signedReversalUnit R r)⁻¹) : Mat R r) =
      ((-1 : R) ^ r) • (signedReversalUnit R r : Mat R r) := by
  rw [signedReversalUnit_inv_eq_transpose, signedReversalUnit_transpose]

end SymmetricSubgroupAsymptotics.CFSGTwistedANaturalMatrices
