import SymmetricSubgroupAsymptotics.CFSGOrthogonalDRootBasisAction
import SymmetricSubgroupAsymptotics.CFSGSymplecticSimpleWeyl
import SymmetricSubgroupAsymptotics.CFSGMatrixDisjointPairRotations

/-! A chain Weyl word in the original type-D root matrices is a pair
of disjoint quarter-turns. It has fourth power one and is not scalar,
uniformly in the characteristic. This is a matrix identity, not yet a
claim about a projective Serre quotient. -/
set_option autoImplicit false
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDSerreMatrices
variable (K : Type) [Field K]

def chainWeylMatrix (r : ℕ) (i : Fin r) : Mat K (r + 1) :=
  (1 - positive K (r + 1) i.castSucc) *
    (1 + negative K (r + 1) i.castSucc) * (1 - positive K (r + 1) i.castSucc)

theorem chainWeylMatrix_rotation (r : ℕ) (i : Fin r) :
    chainWeylMatrix K r i =
      CFSGMatrixPairRotation.rotation K (Sum.inl i.castSucc) (Sum.inl i.succ) *
        CFSGMatrixPairRotation.rotation K (Sum.inr i.castSucc) (Sum.inr i.succ) := by
  have hp := chain_positive_eq_symplectic K (r + 1) i.castSucc (by simp)
  have hn : negative K (r + 1) i.castSucc =
      CFSGSymplecticSerreMatrices.negative K (r + 1) i.castSucc := by
    rw [negative, CFSGSymplecticSerreMatrices.negative, hp]
  have hs := CFSGSymplecticSerreMatrices.simpleWeyl_chain_val K r i
  change (1 + (-1 : K) • CFSGSymplecticSerreMatrices.positive K (r + 1) i.castSucc) *
      (1 + (1 : K) • CFSGSymplecticSerreMatrices.negative K (r + 1) i.castSucc) *
      (1 + (-1 : K) • CFSGSymplecticSerreMatrices.positive K (r + 1) i.castSucc) = _ at hs
  simpa only [chainWeylMatrix, hp, hn, neg_one_smul, one_smul,
    ← sub_eq_add_neg] using hs

theorem chainWeylMatrix_four (r : ℕ) (i : Fin r) : chainWeylMatrix K r i ^ 4 = 1 := by
  have hi : i.castSucc ≠ i.succ := by
    intro h
    have hv := congrArg Fin.val h
    change i.val = i.val + 1 at hv
    omega
  rw [chainWeylMatrix_rotation]
  apply CFSGMatrixPairRotation.disjoint_rotation_four
  · exact fun h => hi (Sum.inl.inj h)
  · exact fun h => hi (Sum.inr.inj h)
  all_goals intro h; cases h

theorem chainWeylMatrix_nonscalar (r : ℕ) (i : Fin r) (c : K) :
    chainWeylMatrix K r i ≠ c • (1 : Mat K (r + 1)) := by
  have hi : i.castSucc ≠ i.succ := by
    intro h
    have hv := congrArg Fin.val h
    change i.val = i.val + 1 at hv
    omega
  intro h
  have hv := congrArg (fun M : Mat K (r + 1) => M *ᵥ Pi.single (Sum.inl i.castSucc) 1) h
  dsimp only at hv
  rw [chainWeylMatrix_rotation, ← Matrix.mulVec_mulVec,
    CFSGMatrixPairRotation.rotation_basis_other K _ _ _
      (by intro h; cases h) (by intro h; cases h),
    CFSGMatrixPairRotation.rotation_basis_left K _ _ (fun h => hi (Sum.inl.inj h)),
    Matrix.smul_mulVec, Matrix.one_mulVec] at hv
  have he := congrFun hv (Sum.inl i.succ)
  simpa [Pi.single_apply, hi, Ne.symm hi] using he

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDSerreMatrices
