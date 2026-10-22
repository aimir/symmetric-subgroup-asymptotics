import SymmetricSubgroupAsymptotics.CFSGGeneratedOrbitConstancy
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBSimpleMaximalOverlap
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBMaximalSubspaceOrbit
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationElements
import SymmetricSubgroupAsymptotics.CFSGMatrixSubspaceUnitAction

/-! The original maximal singular B spaces are connected by overlaps
of codimension at most one. Every translated simple-root step has the
proved overlap dimension; actual root-word transitivity supplies all
vertices. Thus any locally constant field assignment is globally constant. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBMaximalOverlapConstancy
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBPositiveSubspace CFSGPolarSubspacePoints
open CFSGOrthogonalBMaximalSubspaceOrbit CFSGOrthogonalBSingularVectorCount
open CFSGOrthogonalBGenerationElements CFSGOrthogonalBSimpleMaximalOverlap
variable (K : Type) [Field K] [Finite K]

theorem constant_on_maximal_spaces {Y : Type*} (h2 : (2 : K) ≠ 0) (n : ℕ)
    (φ : Subspaces (gram K n).toBilin'→Y)
    (hlocal : ∀W Z : Subspaces (gram K n).toBilin',
      Module.finrank K W.val=n → Module.finrank K Z.val=n →
      n≤Module.finrank K (W.val⊓Z.val : Submodule K (Index n→K))+1 → φ W=φ Z)
    (W : Subspaces (gram K n).toBilin') (hW : Module.finrank K W.val=n) :
    φ W=φ ⟨positiveSubspace K n,positiveSubspace_singular K n⟩ := by
  let P : Subspaces (gram K n).toBilin' :=
    ⟨positiveSubspace K n,positiveSubspace_singular K n⟩
  let F : elementaryRootGroup K n→Y := fun g=>φ (naturalSubspace K h2 n g P)
  have hstep : ∀a ε i t,F (a*rootElement K n ε i t)=F a := by
    intro a ε i t
    let b := rootElement K n ε i t
    let e := naturalLinearEquiv K n a
    have hmap : (naturalSubspace K h2 n (a*b) P).val=
        (naturalSubspace K h2 n b P).val.map e.toLinearMap := by
      change P.val.map (Matrix.mulVecLin ((a*b).val : Mat K n))=
        (P.val.map (Matrix.mulVecLin (b.val : Mat K n))).map
          (Matrix.mulVecLin (a.val : Mat K n))
      change P.val.map (Matrix.mulVecLin ((a.val : Mat K n)*(b.val : Mat K n)))=_
      rw [Matrix.mulVecLin_mul,Submodule.map_comp]
    have hdim : Module.finrank K
        ((naturalSubspace K h2 n a P).val⊓(naturalSubspace K h2 n (a*b) P).val :
          Submodule K (Index n→K))=
        Module.finrank K (P.val⊓(naturalSubspace K h2 n b P).val : Submodule K (Index n→K)) := by
      rw [hmap]
      change Module.finrank K (P.val.map e.toLinearMap⊓
        (naturalSubspace K h2 n b P).val.map e.toLinearMap : Submodule K (Index n→K))=_
      rw [←Submodule.map_inf e.toLinearMap e.injective,e.finrank_map_eq]
    have hbound : n≤Module.finrank K
        ((naturalSubspace K h2 n a P).val⊓(naturalSubspace K h2 n (a*b) P).val :
          Submodule K (Index n→K))+1 := by
      rw [hdim]
      exact root_positive_intersection_finrank K n ε i t
    exact (hlocal (naturalSubspace K h2 n a P) (naturalSubspace K h2 n (a*b) P)
      ((naturalSubspace_finrank K h2 n a P).trans (positiveSubspace_finrank K n))
      ((naturalSubspace_finrank K h2 n (a*b) P).trans (positiveSubspace_finrank K n)) hbound).symm
  have hF : ∀g,F g=F 1 := CFSGGeneratedOrbitConstancy.constant_of_generating_right_steps
    _ (rootElements_generate K n) F (by rintro a b ⟨ε,i,t,rfl⟩;exact hstep a ε i t)
  obtain ⟨g,hg⟩ := exists_normalize_full_rank K h2 n W hW
  have hi := congrArg (fun T : Submodule K (Index n→K)=>
    T.map (Matrix.mulVecLin ((g.val⁻¹ : (Mat K n)ˣ) : Mat K n))) hg
  dsimp only at hi
  rw [←CFSGMatrixSubspaceUnitAction.map_mul,inv_mul_cancel,Units.val_one,
    CFSGMatrixSubspaceUnitAction.map_one] at hi
  have he : W=naturalSubspace K h2 n g⁻¹ P := Subtype.ext hi
  have hP : naturalSubspace K h2 n 1 P=P := by
    apply Subtype.ext
    change P.val.map (Matrix.mulVecLin (1 : Mat K n))=P.val
    exact CFSGMatrixSubspaceUnitAction.map_one P.val
  rw [he]
  exact (hF g⁻¹).trans (congrArg φ hP)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBMaximalOverlapConstancy
