import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIntegralRealization
import SymmetricSubgroupAsymptotics.CFSGSerreDividedPowerPaths

/-! Literal original D source paths, before spanning or faithfulness.
All positive roots use first divided powers. The fork seed is the actual
terminal generator, not a new matrix lift. Negative paths retain signs. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDOriginalRootCandidates
open CFSG.Models.Chevalley CFSGSerreDiagram CFSGSerreDividedPowerPaths
variable (r : ℕ)
abbrev Source := integralLattice (CartanMatrix.D r)
abbrev Pair := {ij : Fin r×Fin r // ij.1.val < ij.2.val}
abbrev RootIndex := Pair r ⊕ Pair r
abbrev BasisIndex := Fin r ⊕ (Bool×RootIndex r)

def descend (i j : Fin r) : List (Fin r) :=
  List.ofFn (fun k : Fin (j.val-i.val)=>
    (⟨j.val-1-k.val,by have h:=j.isLt; omega⟩ : Fin r))

def steps (nodes : List (Fin r)) : List (Fin r×ℕ) := nodes.map (fun i=>(i,1))

def path (neg : Bool) (start : Fin r) (nodes : List (Fin r)) : Source r :=
  (if neg then (-1:ℤ)^nodes.length else 1) •
    pathVector (CartanMatrix.D r) neg start (steps r nodes)

def difference (neg : Bool) (ij : Pair r) : Source r :=
  let start : Fin r:=⟨ij.val.2.val-1,by have h:=ij.val.2.isLt; omega⟩
  path r neg start (descend r ij.val.1 start)

def sumRoot (hr : 4 ≤ r) (neg : Bool) (ij : Pair r) : Source r :=
  let last : Fin r:=⟨r-1,by omega⟩
  let previous : Fin r:=⟨r-2,by omega⟩
  path r neg last (descend r ij.val.1 previous ++ descend r ij.val.2 last)

def root (hr : 4 ≤ r) (neg : Bool) : RootIndex r→Source r
  | .inl ij => difference r neg ij
  | .inr ij => sumRoot r hr neg ij

def vector (hr : 4 ≤ r) : BasisIndex r→Source r
  | .inl i => latticeGenerator (CartanMatrix.D r) (.H i)
  | .inr (neg,j) => root r hr neg j

theorem descend_self (i : Fin r) : descend r i i=[] := by simp [descend]

theorem original_generators_mem (hr : 4 ≤ r) (g : CartanMatrix.Generators (Fin r)) :
    latticeGenerator (CartanMatrix.D r) g∈
      Submodule.span ℤ (Set.range (vector r hr)) := by
  apply Submodule.subset_span
  cases g with
  | H i => exact ⟨.inl i,rfl⟩
  | E i =>
    by_cases hi : i.val+1 < r
    · let next : Fin r:=⟨i.val+1,hi⟩
      let ij : Pair r:=⟨(i,next),by dsimp [next]; omega⟩
      refine ⟨.inr (false,.inl ij),?_⟩
      simp [vector,root,difference,ij,next,descend,steps,path,pathVector,applySteps]
    · let previous : Fin r:=⟨r-2,by omega⟩
      have hil : i.val=r-1:=by have h:=i.isLt; omega
      let ij : Pair r:=⟨(previous,i),by dsimp [previous]; omega⟩
      have hlast : (⟨r-1,by omega⟩ : Fin r)=i:=Fin.ext hil.symm
      refine ⟨.inr (false,.inr ij),?_⟩
      simp [vector,root,sumRoot,ij,previous,hlast,descend_self,steps,path,pathVector,applySteps]
  | F i =>
    by_cases hi : i.val+1 < r
    · let next : Fin r:=⟨i.val+1,hi⟩
      let ij : Pair r:=⟨(i,next),by dsimp [next]; omega⟩
      refine ⟨.inr (true,.inl ij),?_⟩
      simp [vector,root,difference,ij,next,descend,steps,path,pathVector,applySteps]
    · let previous : Fin r:=⟨r-2,by omega⟩
      have hil : i.val=r-1:=by have h:=i.isLt; omega
      let ij : Pair r:=⟨(previous,i),by dsimp [previous]; omega⟩
      have hlast : (⟨r-1,by omega⟩ : Fin r)=i:=Fin.ext hil.symm
      refine ⟨.inr (true,.inr ij),?_⟩
      simp [vector,root,sumRoot,ij,previous,hlast,descend_self,steps,path,pathVector,applySteps]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDOriginalRootCandidates
