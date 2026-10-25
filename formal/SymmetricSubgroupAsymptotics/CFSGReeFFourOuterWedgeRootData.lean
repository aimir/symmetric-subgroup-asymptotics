import SymmetricSubgroupAsymptotics.CFSGReeFFourOuterStarColumns
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRaisedRoot
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylWordDegree

/-! The six literal E6 roots on the node-1 A3 wedge slice.
Labels are the lexicographic pairs 01,02,03,12,13,23. Their root sums,
reflections and zero-or-one pairings are integral statements, before any
field or Ree fixedness specialization. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOuterWedgeRootData
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoCoordinatePositiveRootGenerators CFSGExceptionalNormTwoBases
open CFSGExceptionalCartanPositiveDefinite CFSGReeFFourOuterStarColumns
open CFSGNormTwoCoordinateRaisedRoot CFSGNormTwoGeckWeylWordDegree
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos

def wedgeRow : Fin 6 → Fin 6 → ℤ :=
  ![![0,1,0,0,0,0], ![0,1,0,1,0,0], ![0,1,0,1,1,0],
    ![0,1,1,1,0,0], ![0,1,1,1,1,0], ![0,1,1,2,1,0]]

def wedgeRoot (k : Fin 6) : PositiveRoot A :=
  ⟨⟨wedgeRow k,by fin_cases k <;> decide⟩,by fin_cases k <;> decide⟩

def raiseSource : Fin 3 → Fin 2 → Fin 6 := ![![1,2],![0,4],![1,3]]
def raiseTarget : Fin 3 → Fin 2 → Fin 6 := ![![3,4],![1,5],![2,4]]

def wedgeSwap (j : Fin 3) : Equiv.Perm (Fin 6) :=
  ![Equiv.swap 1 3*Equiv.swap 2 4,
    Equiv.swap 0 1*Equiv.swap 4 5,
    Equiv.swap 1 2*Equiv.swap 3 4] j

theorem pair_zero_or_one (i j : Fin 6) (hij : i≠j) :
    integerPairing A (wedgeRoot i).val.val (wedgeRoot j).val.val=0 ∨
      integerPairing A (wedgeRoot i).val.val (wedgeRoot j).val.val=1 := by
  have h : ∀i j : Fin 6,i≠j → integerPairing A (wedgeRow i) (wedgeRow j)=0 ∨
      integerPairing A (wedgeRow i) (wedgeRow j)=1 := by decide
  exact h i j hij

theorem simple_pair_shape (j : Fin 3) (k : Fin 6) :
    integerPairing A (wedgeRoot k).val.val (E6Index (leftStar.step j) : Roots A).val=
      if k=raiseSource j 0 ∨ k=raiseSource j 1 then -1
      else if k=raiseTarget j 0 ∨ k=raiseTarget j 1 then 1 else 0 := by
  change integerPairing A (wedgeRow k) (Pi.single (leftStar.step j) 1)=_
  fin_cases j <;> fin_cases k <;> decide

theorem raised_root (j : Fin 3) (a : Fin 2)
    (hpair : integerPairing A (wedgeRoot (raiseSource j a)).val.val
      (E6Index (leftStar.step j) : Roots A).val= -1) :
    raisedRoot A hd hs hp ho (wedgeRoot (raiseSource j a)).val (leftStar.step j) hpair=
      (wedgeRoot (raiseTarget j a)).val := by
  apply Subtype.ext
  change wedgeRow (raiseSource j a)+Pi.single (leftStar.step j) 1=
    wedgeRow (raiseTarget j a)
  fin_cases j <;> fin_cases a <;> decide

theorem reflected_root (j : Fin 3) (k : Fin 6) :
    wordRoot A hs hp E6Base E6Index [leftStar.step j] (wedgeRoot k).val=
      (wedgeRoot (wedgeSwap j k)).val := by
  apply Subtype.ext
  change wedgeRow k-integerPairing A (wedgeRow k) (Pi.single (leftStar.step j) 1) •
    (Pi.single (leftStar.step j) 1)=wedgeRow (wedgeSwap j k)
  fin_cases j <;> fin_cases k <;> decide

end SymmetricSubgroupAsymptotics.CFSGReeFFourOuterWedgeRootData
