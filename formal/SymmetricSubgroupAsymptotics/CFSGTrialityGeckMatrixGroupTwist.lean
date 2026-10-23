import SymmetricSubgroupAsymptotics.CFSGTrialityGeckSourceWordAction
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckRootSubgroupTwist

/-! The actual diagram-field twist preserves the entire literal natural
elementary group, with its checked original simple-root formula. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckMatrixGroupTwist
open CFSGTrialityGeckSourceWordAction CFSGTrialityGeckMatrixTwist
open CFSGTrialityGeckRootSubgroupTwist CFSGTrialityGeckDiagramCovariance
open CFSGSerreQuadraticMatrix CFSGSerreDiagram

theorem matrixGroup_twist_map (K : Type) [Field K] (σ : K ≃+* K) :
    (MatrixGroup K).map (unitTwist K σ).toMonoidHom = MatrixGroup K := by
  apply le_antisymm
  · apply Subgroup.map_le_iff_le_comap.mpr
    apply (Subgroup.closure_le _).mpr
    rintro u ⟨neg,i,t,rfl⟩
    change unitTwist K σ (canonicalRoot rawData K neg i t) ∈ MatrixGroup K
    rw [unitTwist_raw_root]
    exact Subgroup.subset_closure ⟨neg,trialityPermutation i,σ t,rfl⟩
  · apply (Subgroup.closure_le _).mpr
    rintro u ⟨neg,i,t,rfl⟩
    refine ⟨canonicalRoot rawData K neg (trialityPermutation.symm i) (σ.symm t),
      Subgroup.subset_closure ⟨neg,trialityPermutation.symm i,σ.symm t,rfl⟩,?_⟩
    change unitTwist K σ (canonicalRoot rawData K neg (trialityPermutation.symm i) (σ.symm t)) = _
    rw [unitTwist_raw_root,Equiv.apply_symm_apply,RingEquiv.apply_symm_apply]

def matrixGroupTwist (K : Type) [Field K] (σ : K ≃+* K) : MulAut (MatrixGroup K) :=
  ((unitTwist K σ).subgroupMap (MatrixGroup K)).trans
    (MulEquiv.subgroupCongr (matrixGroup_twist_map K σ))

theorem matrixGroupTwist_val (K : Type) [Field K] (σ : K ≃+* K) (g : MatrixGroup K) :
    (matrixGroupTwist K σ g).val = unitTwist K σ g.val := rfl

theorem matrixGroupTwist_root (K : Type) [Field K] (σ : K ≃+* K)
    (neg : Bool) (i : Fin 4) (t : K) :
    matrixGroupTwist K σ (canonicalElementaryRoot rawData K neg i t) =
      canonicalElementaryRoot rawData K neg (trialityPermutation i) (σ t) := by
  apply Subtype.ext
  rw [matrixGroupTwist_val]
  exact unitTwist_raw_root K σ neg i t

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckMatrixGroupTwist
