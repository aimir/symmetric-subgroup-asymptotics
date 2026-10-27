import SymmetricSubgroupAsymptotics.CFSGSymplecticOriginalPositiveBaseActions
import SymmetricSubgroupAsymptotics.CFSGSymplecticOriginalRootParents
import SymmetricSubgroupAsymptotics.CFSGSerreSimpleRootLocalNilpotence

/-! Every nonsimple original positive source path has an actual first-root
parent, with coefficient 1 or 2. Its literal natural coefficient row is
derived by applying the representation, not assumed as a root table. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticOriginalPositiveInductionParents
open CFSG.Models.Chevalley CFSGSerreDiagram CFSGSerreSignedRootWeights
open CFSGSerreLocalNilpotence CFSGSymplecticSerreMatrices
open CFSGSymplecticOriginalRootCandidates CFSGSymplecticOriginalRootParents
open CFSGSymplecticUniformPositiveProfile CFSGSymplecticUniformPositiveTables
open CFSGSymplecticOriginalPositiveSourceWeights
open CFSGSymplecticOriginalPositiveWeightIdentification
variable (r : ℕ)

private theorem parent_row (i : Fin r) (p j : PositiveIndex r) (c : ℚ)
    (hp : ⁅rootVector (CartanMatrix.C r).transpose false i,source r p⁆=c • source r j) :
    raising r i p=c • Pi.single j 1 := by
  have h:=congrArg (fun x=>positiveCoordinates r (rationalSymplecticRepresentation r x)) hp
  simpa only [LieHom.map_lie,map_smul,rationalRepresentation_rootVector,source_image,
    rootMatrix,Bool.false_eq_true,if_false,positive_coordinates_matrix,raising] using h

theorem induction_parent (j : PositiveIndex r) (hj : 1 < height r j) :
    ∃ (i : Fin r) (p : PositiveIndex r) (c : ℚ),c≠0 ∧ 0 < height r p ∧
      height r p+1=height r j ∧
      ⁅rootVector (CartanMatrix.C r).transpose false i,source r p⁆=c • source r j ∧
      raising r i p=c • Pi.single j 1 := by
  rcases j with b | (ij | (i | ij))
  · simp [height] at hj
  · let i:=ij.val.1
    let k:=ij.val.2
    have hik : i.val+1 < k.val := by
      change 1 < k.val-i.val at hj
      omega
    let next : Fin r:=⟨i.val+1,by have h:=k.isLt; omega⟩
    let pk : Pair r:=⟨(next,k),hik⟩
    let p : PositiveIndex r:=.inr (.inl pk)
    have hp : ⁅rootVector (CartanMatrix.C r).transpose false i,source r p⁆=
        (1:ℚ) • source r (.inr (.inl ij)) := by
      have h:=congrArg Subtype.val (positive_difference_parent r i k hik)
      simpa only [integralOperator_one_coe_apply,LieAlgebra.ad_apply,
        source,root,p,pk,next,i,k,one_smul] using h
    refine ⟨i,p,1,by norm_num,?_,?_,hp,parent_row r i p _ 1 hp⟩
    · change 0 < k.val-(i.val+1)
      omega
    · change k.val-(i.val+1)+1=k.val-i.val
      omega
  · have hi:=i.isLt
    have hir : i.val+1 < r := by
      change 1 < 2*(r-i.val)-1 at hj
      omega
    let next : Fin r:=⟨i.val+1,hir⟩
    let pair : Pair r:=⟨(i,next),by dsimp [next]; omega⟩
    let p : PositiveIndex r:=.inr (.inr (.inr pair))
    have hp : ⁅rootVector (CartanMatrix.C r).transpose false i,source r p⁆=
        (2:ℚ) • source r (.inr (.inr (.inl i))) := by
      have h:=congrArg Subtype.val (adjacent_sum_long_parent r i hir)
      simpa only [integralOperator_one_coe_apply,LieAlgebra.ad_apply,
        two_nsmul,two_smul,Submodule.coe_add,source,root,p,pair,next] using h
    refine ⟨i,p,2,by norm_num,?_,?_,hp,parent_row r i p _ 2 hp⟩
    · change 0 < (r-1-i.val)+(r-(i.val+1))
      omega
    · change (r-1-i.val)+(r-(i.val+1))+1=2*(r-i.val)-1
      omega
  · let i:=ij.val.1
    let k:=ij.val.2
    have hik : i.val < k.val:=ij.property
    have hkr:=k.isLt
    by_cases hadj : i.val+1 < k.val
    · let next : Fin r:=⟨i.val+1,by omega⟩
      let pk : Pair r:=⟨(next,k),hadj⟩
      let p : PositiveIndex r:=.inr (.inr (.inr pk))
      have hp : ⁅rootVector (CartanMatrix.C r).transpose false i,source r p⁆=
          (1:ℚ) • source r (.inr (.inr (.inr ij))) := by
        have h:=congrArg Subtype.val (positive_sum_parent r i k hadj)
        simpa only [integralOperator_one_coe_apply,LieAlgebra.ad_apply,
          source,root,p,pk,next,i,k,one_smul] using h
      refine ⟨i,p,1,by norm_num,?_,?_,hp,parent_row r i p _ 1 hp⟩
      · change 0 < (r-1-(i.val+1))+(r-k.val)
        omega
      · change (r-1-(i.val+1))+(r-k.val)+1=(r-1-i.val)+(r-k.val)
        omega
    · have he : k.val=i.val+1:=by omega
      have hir : i.val+1 < r:=by omega
      let p : PositiveIndex r:=.inr (.inr (.inl k))
      have hp : ⁅rootVector (CartanMatrix.C r).transpose false i,source r p⁆=
          (1:ℚ) • source r (.inr (.inr (.inr ij))) := by
        have hk : (⟨i.val+1,hir⟩ : Fin r)=k:=Fin.ext he.symm
        have h:=congrArg Subtype.val (adjacent_sum_parent r i hir)
        simpa only [integralOperator_one_coe_apply,LieAlgebra.ad_apply,
          source,root,p,hk,i,k,one_smul] using h
      refine ⟨i,p,1,by norm_num,?_,?_,hp,parent_row r i p _ 1 hp⟩
      · change 0 < 2*(r-k.val)-1
        omega
      · change 2*(r-k.val)-1+1=(r-1-i.val)+(r-k.val)
        omega

end SymmetricSubgroupAsymptotics.CFSGSymplecticOriginalPositiveInductionParents
