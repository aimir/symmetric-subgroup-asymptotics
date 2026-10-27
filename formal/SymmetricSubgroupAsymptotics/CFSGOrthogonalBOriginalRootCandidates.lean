import SymmetricSubgroupAsymptotics.CFSGOrthogonalBIntegralRealization
import SymmetricSubgroupAsymptotics.CFSGSerreDividedPowerPaths

/-! Explicit vectors in the SAME original B-transpose integral Serre lattice.
No spanning, independence, source simplicity or realization faithfulness is
assumed. The terminal second divided power in sum roots keeps the primitive
integral normalization; these vectors are not chosen lifts from a matrix image. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBOriginalRootCandidates
open CFSG.Models.Chevalley CFSGSerreDiagram
open CFSGOrthogonalBSerreMatrices
variable (r : ℕ)

abbrev Source := integralLattice (CartanMatrix.B r).transpose
abbrev Pair := {ij : Fin r × Fin r // ij.1.val < ij.2.val}
abbrev RootIndex := Pair r ⊕ (Fin r ⊕ Pair r)
abbrev BasisIndex := Fin r ⊕ (Bool × RootIndex r)

/-- Nodes j-1,j-2,...,i, applied in that order. -/
def descend (i j : Fin r) : List (Fin r) :=
  List.ofFn (fun k : Fin (j.val - i.val) =>
    (⟨j.val - 1 - k.val, by omega⟩ : Fin r))

def steps (nodes : List (Fin r)) (power : ℕ) : List (Fin r × ℕ) :=
  nodes.map (fun i => (i, power))

def path (neg : Bool) (start : Fin r) (ss : List (Fin r × ℕ)) : Source r :=
  (if neg then (-1 : ℤ) ^ (ss.map Prod.snd).sum else 1) •
    CFSGSerreDividedPowerPaths.pathVector (CartanMatrix.B r).transpose neg start ss

/-- A long difference root e_i-e_j, with first divided powers. -/
def difference (neg : Bool) (ij : Pair r) : Source r :=
  let start : Fin r := ⟨ij.val.2.val - 1, by have h := ij.property; omega⟩
  path r neg start (steps r (descend r ij.val.1 start) 1)

/-- A short root e_i, descending from the terminal simple short root. -/
def short (neg : Bool) (i : Fin r) : Source r :=
  let last : Fin r := ⟨r - 1, by have h := i.isLt; omega⟩
  path r neg last (steps r (descend r i last) 1)

/-- A long sum root e_i+e_j. The terminal second divided power converts
`e_i-e_last` to `-(e_i+e_last)` before the second index descends. -/
def sumRoot (neg : Bool) (ij : Pair r) : Source r :=
  let last : Fin r := ⟨r - 1, by have h := ij.val.2.isLt; omega⟩
  let previous : Fin r := ⟨r - 2, by
    have h := ij.property
    have hlast := ij.val.2.isLt
    omega⟩
  (-1 : ℤ) • path r neg previous
    (steps r (descend r ij.val.1 previous) 1 ++
      [(last, 2)] ++ steps r (descend r ij.val.2 last) 1)

def root (neg : Bool) : RootIndex r → Source r
  | .inl ij => difference r neg ij
  | .inr (.inl i) => short r neg i
  | .inr (.inr ij) => sumRoot r neg ij

def vector : BasisIndex r → Source r
  | .inl i => latticeGenerator (CartanMatrix.B r).transpose (.H i)
  | .inr (neg, j) => root r neg j

theorem descend_self (i : Fin r) : descend r i i = [] := by
  simp [descend]

/-- All original H/E/F generators lie in the actual candidate span.
This is only the generator part of the future source-spanning argument. -/
theorem generator_mem_span (g : CartanMatrix.Generators (Fin r)) :
    generator (CartanMatrix.B r).transpose g ∈
      Submodule.span ℤ (Set.range (fun j => (vector r j).val)) := by
  apply Submodule.subset_span
  cases g with
  | H i => exact ⟨Sum.inl i, rfl⟩
  | E i =>
    by_cases h : i.val + 1 < r
    · let j : Fin r := ⟨i.val + 1, h⟩
      let ij : Pair r := ⟨(i, j), by dsimp [j]; omega⟩
      refine ⟨Sum.inr (false, Sum.inl ij), ?_⟩
      simp only [vector, root, difference]
      change (path r false _ _).val = _
      simp [path, steps, descend, ij, j, CFSGSerreDividedPowerPaths.pathVector,
        CFSGSerreDividedPowerPaths.applySteps, latticeGenerator]
    · refine ⟨Sum.inr (false, Sum.inr (Sum.inl i)), ?_⟩
      have hi : (⟨r - 1, by have hlt := i.isLt; omega⟩ : Fin r) = i := by
        apply Fin.ext
        change r - 1 = i.val
        have hlt := i.isLt
        omega
      simp [vector, root, short, hi, descend_self, steps, path,
        CFSGSerreDividedPowerPaths.pathVector,
        CFSGSerreDividedPowerPaths.applySteps, latticeGenerator]
  | F i =>
    by_cases h : i.val + 1 < r
    · let j : Fin r := ⟨i.val + 1, h⟩
      let ij : Pair r := ⟨(i, j), by dsimp [j]; omega⟩
      refine ⟨Sum.inr (true, Sum.inl ij), ?_⟩
      simp [vector, root, difference, path, steps, descend, ij, j,
        CFSGSerreDividedPowerPaths.pathVector,
        CFSGSerreDividedPowerPaths.applySteps, latticeGenerator]
    · refine ⟨Sum.inr (true, Sum.inr (Sum.inl i)), ?_⟩
      have hi : (⟨r - 1, by have hlt := i.isLt; omega⟩ : Fin r) = i := by
        apply Fin.ext
        change r - 1 = i.val
        have hlt := i.isLt
        omega
      simp [vector, root, short, hi, descend_self, steps, path,
        CFSGSerreDividedPowerPaths.pathVector,
        CFSGSerreDividedPowerPaths.applySteps, latticeGenerator]

/-- Matrix execution of the same integral divided-power instruction list. -/
def matrixSteps (neg : Bool) : List (Fin r × ℕ) → Mat ℤ r → Mat ℤ r
  | [], x => x
  | s :: ss, x => matrixSteps neg ss
      (CFSGIntegralQuadraticRootOperators.operator ℤ
        (rootMatrix ℤ r neg s.1) (rootSecond ℤ r neg s.1) s.2 x)

theorem applySteps_image (neg : Bool) (ss : List (Fin r × ℕ)) (x : Source r) :
    integralOrthogonalRepresentation r
      (CFSGSerreDividedPowerPaths.applySteps (CartanMatrix.B r).transpose neg ss x) =
      matrixSteps r neg ss (integralOrthogonalRepresentation r x) := by
  induction ss generalizing x with
  | nil => rfl
  | cons s ss ih =>
    change integralOrthogonalRepresentation r
      (CFSGSerreDividedPowerPaths.applySteps _ neg ss
        (integralOperator _ neg s.1 s.2 x)) = _
    rw [ih, CFSGSerreQuadraticMatrix.integralRepresentation_operator]
    cases neg <;> rfl

theorem path_image (neg : Bool) (start : Fin r) (ss : List (Fin r × ℕ)) :
    integralOrthogonalRepresentation r (path r neg start ss) =
      (if neg then (-1 : ℤ) ^ (ss.map Prod.snd).sum else 1) •
        matrixSteps r neg ss
          (integerGenerator r (if neg then .F start else .E start)) := by
  simp only [path, map_smul, CFSGSerreDividedPowerPaths.pathVector]
  rw [applySteps_image]
  exact congrArg
    (fun M => (if neg then (-1 : ℤ) ^ (ss.map Prod.snd).sum else 1) •
      matrixSteps r neg ss M)
    (CFSGSerreQuadraticMatrix.integralRepresentation_generator (realizationData r)
      (if neg then .F start else .E start))

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBOriginalRootCandidates
