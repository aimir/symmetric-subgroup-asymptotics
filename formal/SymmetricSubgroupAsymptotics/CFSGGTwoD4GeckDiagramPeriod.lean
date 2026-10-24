import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMatrixTwist

/-! The literal D4 diagram action has period three on the whole actual
matrix algebra and its units. The proof reads the genuine coordinate
permutation and does not use source or image faithfulness. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckDiagramPeriod

open CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance
open CFSGTrialityGeckMatrixTwist CFSGNormTwoCoordinateDiagramIndices
open CFSGSerreDiagram
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots (CartanMatrix.D 4)) := Classical.decEq _

 theorem trialityIndex_thrice (x : GeckIndex) :
    trialityIndex (trialityIndex (trialityIndex x)) = x := by
  cases x with
  | inl x =>
    obtain ⟨i,rfl⟩ := Index.surjective x
    have hv (j : Fin 4) : trialityIndex (Sum.inl (Index j)) =
        Sum.inl (Index (trialityPermutation j)) := by
      change (Sum.inl (supportPermutation (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
        (CartanMatrix.D_transpose 4) D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4)
        trialityPermutation (Index j)) : GeckIndex) = _
      exact congrArg (fun z : Base.support => (Sum.inl z : GeckIndex))
        (supportPermutation_simple (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
          (CartanMatrix.D_transpose 4) D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4)
          trialityPermutation j)
    rw [hv,hv,hv]
    fin_cases i <;> rfl
  | inr k =>
    change (Sum.inr
      (CFSGNormTwoCartanDiagramRoots.rootPermutation (CartanMatrix.D 4) trialityPermutation triality_preserves
        (CFSGNormTwoCartanDiagramRoots.rootPermutation (CartanMatrix.D 4) trialityPermutation triality_preserves
          (CFSGNormTwoCartanDiagramRoots.rootPermutation (CartanMatrix.D 4) trialityPermutation triality_preserves k))) :
      GeckIndex) = Sum.inr k
    apply congrArg (fun r : CFSGNormTwoRootPairing.Roots (CartanMatrix.D 4) => (Sum.inr r : GeckIndex))
    apply Subtype.ext
    funext i
    change k.val (trialityPermutation.symm (trialityPermutation.symm (trialityPermutation.symm i))) = k.val i
    have ht : ∀ j : Fin 4, trialityPermutation (trialityPermutation (trialityPermutation j)) = j := by
      intro j
      fin_cases j <;> rfl
    apply congrArg k.val
    simpa only [Equiv.apply_symm_apply] using
      (ht (trialityPermutation.symm (trialityPermutation.symm (trialityPermutation.symm i)))).symm

theorem matrixTwist_thrice (K : Type) [CommRing K] (M : Matrix GeckIndex GeckIndex K) :
    matrixTwist K (RingEquiv.refl K)
      (matrixTwist K (RingEquiv.refl K) (matrixTwist K (RingEquiv.refl K) M)) = M := by
  have hi (i : GeckIndex) : trialityIndex.symm (trialityIndex.symm (trialityIndex.symm i)) = i := by
    simpa only [Equiv.apply_symm_apply] using
      (trialityIndex_thrice (trialityIndex.symm (trialityIndex.symm (trialityIndex.symm i)))).symm
  apply Matrix.ext
  intro i j
  change M (trialityIndex.symm (trialityIndex.symm (trialityIndex.symm i)))
    (trialityIndex.symm (trialityIndex.symm (trialityIndex.symm j))) = M i j
  rw [hi,hi]

theorem unitTwist_pow_three (K : Type) [CommRing K] :
    (unitTwist K (RingEquiv.refl K))^3 = 1 := by
  apply MulEquiv.ext
  intro u
  apply Units.ext
  exact matrixTwist_thrice K u.val

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckDiagramPeriod
