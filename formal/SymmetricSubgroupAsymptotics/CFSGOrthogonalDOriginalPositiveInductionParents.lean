import SymmetricSubgroupAsymptotics.CFSGOrthogonalDOriginalPositiveBaseActions
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDOriginalRootParents
import SymmetricSubgroupAsymptotics.CFSGSerreSimpleRootLocalNilpotence

/-! Every nonsimple original positive D path has an actual first-root
parent with coefficient one. Fork right-indices are raised first, exactly
as in the literal source word; no operator commutation is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDOriginalPositiveInductionParents
open CFSG.Models.Chevalley CFSGSerreDiagram CFSGSerreSignedRootWeights
open CFSGSerreLocalNilpotence CFSGOrthogonalDSerreMatrices
open CFSGOrthogonalDOriginalRootCandidates
open CFSGOrthogonalDUniformPositiveProfile CFSGOrthogonalDUniformPositiveTables
open CFSGOrthogonalDOriginalPositiveSourceWeights
open CFSGOrthogonalDOriginalPositiveWeightIdentification
variable (r : ℕ) (hr : 4 ≤ r)

private theorem parent_row (i : Fin r) (p j : PositiveIndex r)
    (hp : ⁅rootVector (CartanMatrix.D r) false i,source r hr p⁆=source r hr j) :
    raising r hr i p=(1:ℚ) • Pi.single j 1 := by
  have h:=congrArg (fun x=>positiveCoordinates r hr (rationalOrthogonalRepresentation r hr x)) hp
  have hE : rationalOrthogonalRepresentation r hr (rootVector (CartanMatrix.D r) false i)=
      positive ℚ r i := rationalOrthogonalRepresentation_E r hr i
  simpa only [LieHom.map_lie,hE,source_image,positive_coordinates_matrix,raising,one_smul] using h

theorem induction_parent (j : PositiveIndex r) (hj : 1 < height r j) :
    ∃ (i : Fin r) (p : PositiveIndex r) (c : ℚ),c≠0 ∧ 0 < height r p ∧
      height r p+1=height r j ∧
      ⁅rootVector (CartanMatrix.D r) false i,source r hr p⁆=c • source r hr j ∧
      raising r hr i p=c • Pi.single j 1 := by
  rcases j with b | (ij | ij)
  · simp [height] at hj
  · let i:=ij.val.1
    let k:=ij.val.2
    have hkr:=k.isLt
    have hik : i.val+1 < k.val := by change 1 < k.val-i.val at hj;omega
    let next : Fin r:=⟨i.val+1,by omega⟩
    let pk : Pair r:=⟨(next,k),hik⟩
    let p : PositiveIndex r:=.inr (.inl pk)
    have hp : ⁅rootVector (CartanMatrix.D r) false i,source r hr p⁆=
        source r hr (.inr (.inl ij)) := by
      have h:=congrArg Subtype.val (CFSGOrthogonalDOriginalRootParents.difference_parent r i k hik)
      simpa only [integralOperator_one_coe_apply,LieAlgebra.ad_apply,
        source,root,p,pk,next,i,k] using h
    refine ⟨i,p,1,by norm_num,?_,?_,by simpa only [one_smul] using hp,parent_row r hr i p _ hp⟩
    · change 0 < k.val-(i.val+1);omega
    · change k.val-(i.val+1)+1=k.val-i.val;omega
  · let i:=ij.val.1
    let k:=ij.val.2
    have hik : i.val < k.val:=ij.property
    have hir:=i.isLt
    have hkr:=k.isLt
    by_cases hk : k.val+1 < r
    · let next : Fin r:=⟨k.val+1,hk⟩
      let pk : Pair r:=⟨(i,next),by dsimp [next];omega⟩
      let p : PositiveIndex r:=.inr (.inr pk)
      have hp : ⁅rootVector (CartanMatrix.D r) false k,source r hr p⁆=
          source r hr (.inr (.inr ij)) := by
        have h:=congrArg Subtype.val
          (CFSGOrthogonalDOriginalRootParents.sum_right_parent r hr i k hik hk)
        simpa only [integralOperator_one_coe_apply,LieAlgebra.ad_apply,
          source,root,p,pk,next,i,k] using h
      refine ⟨k,p,1,by norm_num,?_,?_,by simpa only [one_smul] using hp,parent_row r hr k p _ hp⟩
      · change 0 < (r-2-i.val)+(r-1-(k.val+1))+1;omega
      · change (r-2-i.val)+(r-1-(k.val+1))+1+1=(r-2-i.val)+(r-1-k.val)+1;omega
    · have hklast : k.val=r-1:=by omega
      have hi : i.val+2 < r := by
        change 1 < (r-2-i.val)+(r-1-k.val)+1 at hj
        omega
      let next : Fin r:=⟨i.val+1,by omega⟩
      let pk : Pair r:=⟨(next,k),by dsimp [next];omega⟩
      let p : PositiveIndex r:=.inr (.inr pk)
      have hlast : (⟨r-1,by omega⟩ : Fin r)=k:=Fin.ext hklast.symm
      have hp : ⁅rootVector (CartanMatrix.D r) false i,source r hr p⁆=
          source r hr (.inr (.inr ij)) := by
        have h:=congrArg Subtype.val
          (CFSGOrthogonalDOriginalRootParents.sum_terminal_left_parent r hr i hi)
        simpa only [integralOperator_one_coe_apply,LieAlgebra.ad_apply,
          source,root,p,pk,next,hlast,i,k] using h
      refine ⟨i,p,1,by norm_num,?_,?_,by simpa only [one_smul] using hp,parent_row r hr i p _ hp⟩
      · change 0 < (r-2-(i.val+1))+(r-1-k.val)+1;omega
      · change (r-2-(i.val+1))+(r-1-k.val)+1+1=(r-2-i.val)+(r-1-k.val)+1;omega

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDOriginalPositiveInductionParents
