import SymmetricSubgroupAsymptotics.CFSGOrthogonalDOriginalRootCandidates
import SymmetricSubgroupAsymptotics.CFSGSerreDividedPowerPathComposition
import Mathlib.Data.List.OfFn

/-! Genuine first-action parent equalities in the SAME original D
integral lattice. Right-index parents are used before left-index parents,
so no unstated commutation of source root operators is needed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDOriginalRootParents
open CFSG.Models.Chevalley CFSGOrthogonalDOriginalRootCandidates
open CFSGSerreDividedPowerPathComposition
variable (r : ℕ)

theorem descend_split (i j : Fin r) (hij : i.val < j.val) :
    descend r i j=descend r (⟨i.val+1,by omega⟩ : Fin r) j++[i] := by
  have hn : j.val-i.val=(j.val-(i.val+1))+1:=by omega
  unfold descend
  rw [List.ofFn_congr hn,List.ofFn_succ',List.concat_eq_append]
  congr 1
  apply congrArg (fun x : Fin r=>[x])
  apply Fin.ext
  simp only [Fin.val_cast,Fin.val_last,Fin.val_mk]
  omega

theorem positive_path_snoc (start : Fin r) (ss : List (Fin r)) (i : Fin r) :
    path r false start (ss++[i])=
      integralOperator (CartanMatrix.D r) false i 1 (path r false start ss) := by
  simp only [path,Bool.false_eq_true,if_false,one_smul,steps,List.map_append,
    List.map_cons,List.map_nil,path_append_step]

theorem difference_parent (i j : Fin r) (hij : i.val+1 < j.val) :
    let next : Fin r:=⟨i.val+1,by have h:=j.isLt; omega⟩
    let child : Pair r:=⟨(i,j),by change i.val < j.val; omega⟩
    let parent : Pair r:=⟨(next,j),hij⟩
    integralOperator (CartanMatrix.D r) false i 1 (difference r false parent)=
      difference r false child := by
  dsimp only
  let start : Fin r:=⟨j.val-1,by have h:=j.isLt; omega⟩
  have hs:=descend_split r i start (by dsimp [start]; omega)
  simp only [difference]
  change integralOperator _ false i 1 (path r false start _)=path r false start _
  rw [hs]
  exact (positive_path_snoc r start _ i).symm

theorem sum_right_parent (hr : 4 ≤ r) (i j : Fin r)
    (hij : i.val < j.val) (hj : j.val+1 < r) :
    let next : Fin r:=⟨j.val+1,hj⟩
    let child : Pair r:=⟨(i,j),hij⟩
    let parent : Pair r:=⟨(i,next),by dsimp [next]; omega⟩
    integralOperator (CartanMatrix.D r) false j 1 (sumRoot r hr false parent)=
      sumRoot r hr false child := by
  dsimp only
  let last : Fin r:=⟨r-1,by omega⟩
  have hs:=descend_split r j last (by dsimp [last]; omega)
  simp only [sumRoot]
  change integralOperator _ false j 1 (path r false last _)=path r false last _
  rw [hs,←List.append_assoc]
  exact (positive_path_snoc r last _ j).symm

theorem sum_terminal_left_parent (hr : 4 ≤ r) (i : Fin r) (hi : i.val+2 < r) :
    let last : Fin r:=⟨r-1,by omega⟩
    let next : Fin r:=⟨i.val+1,by omega⟩
    let child : Pair r:=⟨(i,last),by dsimp [last]; omega⟩
    let parent : Pair r:=⟨(next,last),by dsimp [next,last]; omega⟩
    integralOperator (CartanMatrix.D r) false i 1 (sumRoot r hr false parent)=
      sumRoot r hr false child := by
  dsimp only
  let last : Fin r:=⟨r-1,by omega⟩
  let prev : Fin r:=⟨r-2,by omega⟩
  have hs:=descend_split r i prev (by dsimp [prev]; omega)
  simp only [sumRoot,descend_self,List.append_nil]
  change integralOperator _ false i 1 (path r false last _)=path r false last _
  rw [hs]
  exact (positive_path_snoc r last _ i).symm

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDOriginalRootParents
