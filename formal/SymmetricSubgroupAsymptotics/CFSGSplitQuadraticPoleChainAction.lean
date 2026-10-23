import SymmetricSubgroupAsymptotics.CFSGSplitQuadraticPoleRootAction

/-! A negative tail-coordinate parameter of the literal quadratic pole
shear is the actual chain root with its exact minus parameter. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGSplitQuadraticPoleChainAction
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexTailCoordinates
open CFSGSplitQuadraticPoleCoordinates CFSGSplitQuadraticBasisParameters
open CFSGSplitQuadraticPoleRootAction CFSGOrthogonalDGenerationRootArrays
variable (K : Type) [Field K]

theorem negative_single_action (n : ℕ) (j : Fin n) (a : K) (v : Index (n + 1) → K) :
    poleShear K n (Pi.single (Sum.inr j) a) v =
      chainArray (0 : Fin (n + 1)) j.succ (-a) *ᵥ v := by
  apply (coordinateEquiv K n).injective
  change coordinates K n (poleShear K n (Pi.single (Sum.inr j) a) v) =
    coordinates K n (chainArray (0 : Fin (n + 1)) j.succ (-a) *ᵥ v)
  apply Prod.ext
  · change poleShear K n (Pi.single (Sum.inr j) a) v (Sum.inl 0) = _
    rw [positive_head]
    simp [coordinates, negative_norm, negative_polar, chainArray,
      Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.single_mulVec,
      Function.update_apply, tailIndex, Function.comp_apply,
      Fin.succ_ne_zero j, Ne.symm (Fin.succ_ne_zero j)] <;> ring
  · apply Prod.ext
    · funext i
      change poleShear K n (Pi.single (Sum.inr j) a) v (tailIndex n i) = _
      rw [tail_action]
      cases i with
      | inl k =>
        simp [coordinates, chainArray, Matrix.add_mulVec, Matrix.sub_mulVec,
          Matrix.one_mulVec, Matrix.single_mulVec, Function.update_apply,
          tailIndex, Function.comp_apply, Pi.single_apply]
      | inr k =>
        by_cases hk : k = j
        · subst k
          simp [coordinates, chainArray, Matrix.add_mulVec, Matrix.sub_mulVec,
            Matrix.one_mulVec, Matrix.single_mulVec, Function.update_apply,
            tailIndex, Function.comp_apply, Pi.single_apply,
            Fin.succ_ne_zero j, Ne.symm (Fin.succ_ne_zero j)] <;> ring
        · simp [coordinates, chainArray, Matrix.add_mulVec, Matrix.sub_mulVec,
            Matrix.one_mulVec, Matrix.single_mulVec, Function.update_apply,
            tailIndex, Function.comp_apply, Pi.single_apply, hk, Ne.symm hk,
            Fin.succ_ne_zero k, Ne.symm (Fin.succ_ne_zero k)] <;> ring
    · change poleShear K n (Pi.single (Sum.inr j) a) v (Sum.inr 0) = _
      rw [negative_head]
      simp [coordinates, chainArray, Matrix.add_mulVec, Matrix.sub_mulVec,
        Matrix.one_mulVec, Matrix.single_mulVec, Function.update_apply,
        Fin.succ_ne_zero j, Ne.symm (Fin.succ_ne_zero j)]

end SymmetricSubgroupAsymptotics.CFSGSplitQuadraticPoleChainAction
