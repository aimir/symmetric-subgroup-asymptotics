import SymmetricSubgroupAsymptotics.CFSGSymplecticIntegralOperators
import SymmetricSubgroupAsymptotics.CFSGSerreDividedPowerPaths

/-! Actual source candidates, BEFORE any spanning or faithfulness assertion.
The two divided-power steps on long roots retain their primitive integral
normalization. Negative candidates use signed paths in the SAME source,
not lifts chosen from the matrix image. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticOriginalRootCandidates
open CFSG.Models.Chevalley CFSGSerreDiagram
open CFSGSymplecticSerreMatrices
variable (r : ℕ)
abbrev Source := integralLattice (CartanMatrix.C r).transpose
abbrev Pair := {ij : Fin r × Fin r // ij.1.val < ij.2.val}
abbrev RootIndex := Pair r ⊕ (Fin r ⊕ Pair r)
abbrev BasisIndex := Fin r ⊕ (Bool × RootIndex r)

/-- Nodes j-1,j-2,...,i in that order; empty if i=j. -/
def descend (i j : Fin r) : List (Fin r) :=
  List.ofFn (fun k : Fin (j.val-i.val) =>
    (⟨j.val-1-k.val, by omega⟩ : Fin r))

def steps (nodes : List (Fin r)) (power : ℕ) : List (Fin r × ℕ) :=
  nodes.map (fun i => (i,power))

def path (neg : Bool) (start : Fin r) (ss : List (Fin r × ℕ)) : Source r :=
  (if neg then (-1 : ℤ) ^ (ss.map Prod.snd).sum else 1) •
    CFSGSerreDividedPowerPaths.pathVector (CartanMatrix.C r).transpose neg start ss

/-- e_i-e_j: a chain of first divided powers. -/
def difference (neg : Bool) (ij : Pair r) : Source r :=
  let start : Fin r := ⟨ij.val.2.val-1, by have h := ij.property; omega⟩
  path r neg start (steps r (descend r ij.val.1 start) 1)

/-- 2e_i: a chain of SECOND divided powers from the terminal generator. -/
def long (neg : Bool) (i : Fin r) : Source r :=
  let last : Fin r := ⟨r-1, by have h := i.isLt; omega⟩
  path r neg last (steps r (descend r i last) 2)

/-- e_i+e_j: first form 2e_j, then raise the first index to i. -/
def sumRoot (neg : Bool) (ij : Pair r) : Source r :=
  let last : Fin r := ⟨r-1, by have h := ij.val.2.isLt; omega⟩
  path r neg last
    (steps r (descend r ij.val.2 last) 2 ++
      steps r (descend r ij.val.1 ij.val.2) 1)

def root (neg : Bool) : RootIndex r → Source r
  | .inl ij => difference r neg ij
  | .inr (.inl i) => long r neg i
  | .inr (.inr ij) => sumRoot r neg ij

def vector : BasisIndex r → Source r
  | .inl i => latticeGenerator (CartanMatrix.C r).transpose (.H i)
  | .inr (neg,j) => root r neg j

theorem descend_self (i : Fin r) : descend r i i = [] := by
  simp [descend]

/-- All original H/E/F generators occur among these actual candidates.
This verifies the generator half of the lattice-minimality argument. -/
theorem generator_mem_span (g : CartanMatrix.Generators (Fin r)) :
    generator (CartanMatrix.C r).transpose g ∈
      Submodule.span ℤ (Set.range (fun j => (vector r j).val)) := by
  apply Submodule.subset_span
  cases g with
  | H i => exact ⟨Sum.inl i,rfl⟩
  | E i =>
    by_cases h : i.val+1 < r
    · let j : Fin r := ⟨i.val+1,h⟩
      let ij : Pair r := ⟨(i,j),by dsimp [j]; omega⟩
      refine ⟨Sum.inr (false,Sum.inl ij),?_⟩
      simp only [vector,root,difference]
      change (path r false _ _).val = _
      simp [path,steps,descend,ij,j,CFSGSerreDividedPowerPaths.pathVector,
        CFSGSerreDividedPowerPaths.applySteps,latticeGenerator]
    · refine ⟨Sum.inr (false,Sum.inr (Sum.inl i)),?_⟩
      have hi : (⟨r-1,by have hlt := i.isLt; omega⟩ : Fin r)=i := by
        apply Fin.ext
        change r-1=i.val
        have hlt := i.isLt
        omega
      simp [vector,root,long,hi,descend_self,steps,path,
        CFSGSerreDividedPowerPaths.pathVector,
        CFSGSerreDividedPowerPaths.applySteps,latticeGenerator]
  | F i =>
    by_cases h : i.val+1 < r
    · let j : Fin r := ⟨i.val+1,h⟩
      let ij : Pair r := ⟨(i,j),by dsimp [j]; omega⟩
      refine ⟨Sum.inr (true,Sum.inl ij),?_⟩
      simp [vector,root,difference,path,steps,descend,ij,j,
        CFSGSerreDividedPowerPaths.pathVector,
        CFSGSerreDividedPowerPaths.applySteps,latticeGenerator]
    · refine ⟨Sum.inr (true,Sum.inr (Sum.inl i)),?_⟩
      have hi : (⟨r-1,by have hlt := i.isLt; omega⟩ : Fin r)=i := by
        apply Fin.ext
        change r-1=i.val
        have hlt := i.isLt
        omega
      simp [vector,root,long,hi,descend_self,steps,path,
        CFSGSerreDividedPowerPaths.pathVector,
        CFSGSerreDividedPowerPaths.applySteps,latticeGenerator]

/-- Matrix execution of the SAME finite divided-power path. -/
def matrixSteps (neg : Bool) : List (Fin r × ℕ) → Mat ℤ r → Mat ℤ r
  | [],x => x
  | s::ss,x => matrixSteps neg ss
      (CFSGIntegralSquareZeroOperators.operator ℤ (rootMatrix ℤ r neg s.1) s.2 x)

theorem applySteps_image (neg : Bool) (ss : List (Fin r × ℕ)) (x : Source r) :
    integralSymplecticRepresentation r
      (CFSGSerreDividedPowerPaths.applySteps (CartanMatrix.C r).transpose neg ss x) =
      matrixSteps r neg ss (integralSymplecticRepresentation r x) := by
  induction ss generalizing x with
  | nil => rfl
  | cons s ss ih =>
    change integralSymplecticRepresentation r
      (CFSGSerreDividedPowerPaths.applySteps _ neg ss
        (integralOperator _ neg s.1 s.2 x)) = _
    rw [ih,integralRepresentation_operator]
    rfl

end SymmetricSubgroupAsymptotics.CFSGSymplecticOriginalRootCandidates
