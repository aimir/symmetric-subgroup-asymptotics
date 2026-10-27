import SymmetricSubgroupAsymptotics.CFSGOrthogonalDOriginalRootParents
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDOriginalIntegralAction

/-! Whole positive-root images in the SAME original D integral lattice.
Only actual source parents and literal sparse matrix products are used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDOriginalPositiveRootImages
open CFSG.Models.Chevalley CFSGSerreDiagram CFSGOrthogonalDSerreMatrices
open CFSGOrthogonalDOriginalRootCandidates CFSGOrthogonalDOriginalIntegralAction
variable (r : ℕ) (hr : 4 ≤ r)

theorem difference_image (ij : Pair r) :
    integralOrthogonalRepresentation r hr (difference r false ij)=
      CFSGOrthogonalDUniformRootMatrixArithmetic.difference ℤ r ij.val.1 ij.val.2 := by
  suffices h : ∀ n : ℕ,∀ ij : Pair r,ij.val.2.val-ij.val.1.val=n→
      integralOrthogonalRepresentation r hr (difference r false ij)=
        CFSGOrthogonalDUniformRootMatrixArithmetic.difference ℤ r ij.val.1 ij.val.2 by
    exact h _ ij rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro ij hn
    let i:=ij.val.1
    let j:=ij.val.2
    have hij : i.val < j.val:=ij.property
    have hri:=i.isLt
    have hrj:=j.isLt
    have hir : i.val+1 < r:=by omega
    by_cases hadj : i.val+1 < j.val
    · let next : Fin r:=⟨i.val+1,hir⟩
      let parent : Pair r:=⟨(next,j),hadj⟩
      have hp : integralOperator (CartanMatrix.D r) false i 1 (difference r false parent)=
          difference r false ij := by
        exact CFSGOrthogonalDOriginalRootParents.difference_parent r i j hadj
      have hs:=ih (j.val-(i.val+1)) (by change j.val-i.val=n at hn; omega) parent rfl
      rw [←hp,first_image,hs]
      simpa only [rootMatrix,Bool.false_eq_true,if_false,next] using
        CFSGOrthogonalDUniformRootMatrixArithmetic.difference_parent ℤ r i j hir hadj
    · have he : j.val=i.val+1:=by omega
      have hstart : (⟨j.val-1,by omega⟩ : Fin r)=i := by apply Fin.ext; change j.val-1=i.val; omega
      have hsource : difference r false ij=latticeGenerator (CartanMatrix.D r) (.E i) := by
        simp [difference,i,j,hstart,descend_self,path,steps,
          CFSGSerreDividedPowerPaths.pathVector,CFSGSerreDividedPowerPaths.applySteps]
      have hnext : (⟨i.val+1,hir⟩ : Fin r)=j:=Fin.ext he.symm
      rw [hsource,generator_image]
      change positive ℤ r i=CFSGOrthogonalDUniformRootMatrixArithmetic.difference ℤ r i j
      simp only [positive,dif_pos hir,hnext,CFSGOrthogonalDUniformRootMatrixArithmetic.difference]

theorem sum_image (ij : Pair r) :
    integralOrthogonalRepresentation r hr (sumRoot r hr false ij)=
      CFSGOrthogonalDUniformRootMatrixArithmetic.sumRoot ℤ r ij.val.1 ij.val.2 := by
  suffices h : ∀ n : ℕ,∀ ij : Pair r,(r-2-ij.val.1.val)+(r-1-ij.val.2.val)=n→
      integralOrthogonalRepresentation r hr (sumRoot r hr false ij)=
        CFSGOrthogonalDUniformRootMatrixArithmetic.sumRoot ℤ r ij.val.1 ij.val.2 by
    exact h _ ij rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro ij hn
    let i:=ij.val.1
    let j:=ij.val.2
    have hij : i.val < j.val:=ij.property
    have hri:=i.isLt
    have hrj:=j.isLt
    by_cases hj : j.val+1 < r
    · let next : Fin r:=⟨j.val+1,hj⟩
      let parent : Pair r:=⟨(i,next),by dsimp [next]; omega⟩
      have hp : integralOperator (CartanMatrix.D r) false j 1 (sumRoot r hr false parent)=
          sumRoot r hr false ij :=
        CFSGOrthogonalDOriginalRootParents.sum_right_parent r hr i j hij hj
      have hs:=ih ((r-2-i.val)+(r-1-(j.val+1)))
        (by change (r-2-i.val)+(r-1-j.val)=n at hn; omega) parent rfl
      rw [←hp,first_image,hs]
      simpa only [rootMatrix,Bool.false_eq_true,if_false,next] using
        CFSGOrthogonalDUniformRootMatrixArithmetic.sum_right_parent ℤ r i j hj hij
    · have he : j.val=r-1:=by omega
      have hlast : (⟨r-1,by omega⟩ : Fin r)=j:=Fin.ext he.symm
      by_cases hi : i.val+2 < r
      · let next : Fin r:=⟨i.val+1,by omega⟩
        let parent : Pair r:=⟨(next,j),by dsimp [next]; omega⟩
        have hp : integralOperator (CartanMatrix.D r) false i 1 (sumRoot r hr false parent)=
            sumRoot r hr false ij := by
          simpa only [hlast] using
            CFSGOrthogonalDOriginalRootParents.sum_terminal_left_parent r hr i hi
        have hs:=ih ((r-2-(i.val+1))+(r-1-j.val))
          (by change (r-2-i.val)+(r-1-j.val)=n at hn; omega) parent rfl
        rw [←hp,first_image,hs]
        simpa only [rootMatrix,Bool.false_eq_true,if_false,next] using
          CFSGOrthogonalDUniformRootMatrixArithmetic.sum_left_parent ℤ r i j (by omega) (by omega)
      · have hei : i.val=r-2:=by omega
        have hprev : (⟨r-2,by omega⟩ : Fin r)=i:=Fin.ext hei.symm
        have hsource : sumRoot r hr false ij=latticeGenerator (CartanMatrix.D r) (.E j) := by
          simp [sumRoot,i,j,hlast,hprev,descend_self,path,steps,
            CFSGSerreDividedPowerPaths.pathVector,CFSGSerreDividedPowerPaths.applySteps]
        have hp : previous r j=i := by apply Fin.ext; simp only [previous_val]; omega
        rw [hsource,generator_image]
        change positive ℤ r j=CFSGOrthogonalDUniformRootMatrixArithmetic.sumRoot ℤ r i j
        simp only [positive,dif_neg hj,hp,
          CFSGOrthogonalDUniformRootMatrixArithmetic.sumRoot]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDOriginalPositiveRootImages
