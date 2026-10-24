import SymmetricSubgroupAsymptotics.CFSGSerreDividedPowerPaths
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod

/-! A selected 52-vector family in the SAME original F4 integral lattice:
24 positive divided-power paths, their 24 signed counterparts, and four
original Cartan generators. The finite certificates check their weights;
spanning, independence and tensor faithfulness remain separate obligations.
No Roots Fintype or Weyl/action table is evaluated. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGFFourOriginalFiftyTwoFamily
open CFSG.Models.Chevalley CFSGSerreDiagram CFSGSerreDividedPowerPaths
open CFSGSerreSignedRootWeights
local notation "A" => CartanMatrix.F₄

def start (j:Fin 24) : Fin 4 := ![3,2,1,0,2,1,0,1,2,0,2,0,2,2,2,2,2,2,2,2,2,2,2,2] j

def steps (j:Fin 24) : List (Fin 4×ℕ) := ![[],[],[],[],[(3,1)],[(2,1)],[(1,1)],[(2,1),(3,1)],[(1,2)],[(1,1),(2,1)],[(1,2),(3,1)],[(1,1),(2,1),(3,1)],[(1,2),(0,1)],[(1,2),(3,1),(2,1)],[(1,2),(0,1),(3,1)],[(1,2),(0,2)],[(1,2),(0,1),(3,1),(2,1)],[(1,2),(0,2),(3,1)],[(1,2),(0,1),(3,1),(2,1),(1,1)],[(1,2),(0,2),(3,1),(2,1)],[(1,2),(0,2),(3,1),(2,1),(1,1)],[(1,2),(0,2),(3,1),(2,1),(1,2)],[(1,2),(0,2),(3,1),(2,1),(1,2),(2,1)],[(1,2),(0,2),(3,1),(2,1),(1,2),(2,1),(3,1)]] j

def degree (j:Fin 24) : Fin 4→ℤ := ![![0,0,0,1],![0,0,1,0],![0,1,0,0],![1,0,0,0],![0,0,1,1],![0,1,1,0],![1,1,0,0],![0,1,1,1],![0,2,1,0],![1,1,1,0],![0,2,1,1],![1,1,1,1],![1,2,1,0],![0,2,2,1],![1,2,1,1],![2,2,1,0],![1,2,2,1],![2,2,1,1],![1,3,2,1],![2,2,2,1],![2,3,2,1],![2,4,2,1],![2,4,3,1],![2,4,3,2]] j

def simpleWeight (i:Fin 4) (j:Fin 24) : ℤ := ∑k,A i k*degree j k

theorem pathWeight_eq : ∀i:Fin 4,∀j:Fin 24,
    pathWeight A i (start j) (steps j)=(simpleWeight i j:ℚ) := by decide +kernel

theorem positive_weight : ∀j:Fin 24,∃i:Fin 4,0<simpleWeight i j := by decide +kernel

def rootVectors (neg:Bool) (j:Fin 24) : integralLattice A :=
  pathVector A neg (start j) (steps j)

theorem rootVectors_weight (neg:Bool) (i:Fin 4) (j:Fin 24) :
    ⁅coroot A neg i,(rootVectors neg j).val⁆=
      (simpleWeight i j:ℚ) • (rootVectors neg j).val := by
  have h:=pathVector_weight A neg i (start j) (steps j)
  rw [pathWeight_eq] at h
  exact h

abbrev BasisIndex := (Bool×Fin 24)⊕Fin 4

def integralVectors : BasisIndex→integralLattice A :=
  Sum.elim (fun z=>rootVectors z.1 z.2) (fun i=>latticeGenerator A (.H i))

def vectors (j:BasisIndex) : RationalLie A := (integralVectors j).val

theorem basisIndex_card : Nat.card BasisIndex=52 := by
  rw [Nat.card_eq_fintype_card]
  norm_num [Fintype.card_sum,Fintype.card_prod]

end SymmetricSubgroupAsymptotics.CFSGFFourOriginalFiftyTwoFamily
