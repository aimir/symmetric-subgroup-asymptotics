import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryFirstGlobalEntry
import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryOrderedMatrixData
import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryOuterEntryReduction
import SymmetricSubgroupAsymptotics.MatrixBinaryAffineFactor
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! ONE additional universal selected entry through12 actual constant affine factors.
The proof uses symbolic F2 variables, not4096 parameter evaluations.
Original fixed-group parameter/action transport is a separate adapter. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryThirdGlobalColumn
open CFSGReeFFourBinaryOrderedMatrixData MatrixBinaryAffineFactor
open CFSGReeFFourBinaryOuterEntryReduction CFSGReeFFourBinarySeedOuterMatrix

open scoped BigOperators

private theorem two_zero : (2 : ZMod 2)=0 := by decide +kernel
private theorem three_one : (3 : ZMod 2)=1 := by decide +kernel

private abbrev Vec := Fin 26 → ZMod 2

private def StageRelation (A : Mat) (t : ZMod 2) (v w : Vec) : Prop :=
  (affineFactor t A).mulVec v=w

private theorem mulVec_from_rows (A : Mat) (rows : Fin 26 → Finset (Fin 26))
    (hA : ∀i j,A i j=if j∈rows i then 1 else 0) (v : Vec) (i : Fin 26) :
    (A.mulVec v) i=∑j∈rows i,v j := by
  change (∑j : Fin 26,A i j*v j)=∑j∈rows i,v j
  simp_rw [hA]
  simp [ite_mul]

private theorem stage_from_rows (A : Mat) (rows : Fin 26 → Finset (Fin 26))
    (hA : ∀i j,A i j=if j∈rows i then 1 else 0)
    (t : ZMod 2) (v w : Vec)
    (h : ∀i,w i=v i+t*((∑j∈rows i,v j)-v i)) : StageRelation A t v w := by
  unfold StageRelation
  rw [affineFactor_mulVec]
  funext i
  change v i+t*((A.mulVec v) i-v i)=w i
  rw [mulVec_from_rows A rows hA v i]
  exact (h i).symm

private theorem column_from_stage (A C : Mat) (t : ZMod 2) (v w : Vec)
    (hc : C.mulVec (Pi.single 3 1)=v) (hs : StageRelation A t v w) :
    (affineFactor t A*C).mulVec (Pi.single 3 1)=w := by
  rw [←Matrix.mulVec_mulVec,hc]
  exact hs


private def state0 (_b : Fin 12 → ZMod 2) : Vec :=
  ![0,
    0,
    0,
    1,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0 ]

private def state1 (b : Fin 12 → ZMod 2) : Vec :=
  ![0,
    0,
    0,
    1,
    (b 0),
    0,
    (b 0),
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0 ]

private def state2 (b : Fin 12 → ZMod 2) : Vec :=
  ![0,
    0,
    0,
    1,
    (b 0),
    (b 1),
    (b 0)+(b 1)+(b 0)*(b 1),
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0 ]

private def state3 (b : Fin 12 → ZMod 2) : Vec :=
  ![0,
    0,
    0,
    1,
    (b 0),
    (b 1),
    (b 0)+(b 1)+(b 0)*(b 1),
    0,
    0,
    (b 2),
    (b 0)*(b 2),
    (b 2),
    0,
    0,
    0,
    0,
    0,
    (b 2),
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0 ]

private def state4 (b : Fin 12 → ZMod 2) : Vec :=
  ![(b 3),
    (b 3),
    0,
    1,
    (b 0),
    (b 1),
    (b 0)+(b 1)+(b 0)*(b 1),
    0,
    (b 3),
    (b 2),
    (b 0)*(b 2)+(b 1)*(b 3),
    (b 2)+(b 0)*(b 3),
    0,
    0,
    0,
    (b 2)*(b 3),
    0,
    (b 2)+(b 1)*(b 3)+(b 0)*(b 2)*(b 3),
    0,
    (b 0)*(b 3)+(b 2)*(b 3),
    0,
    0,
    0,
    0,
    (b 3),
    0 ]

private def state5 (b : Fin 12 → ZMod 2) : Vec :=
  ![(b 3)+(b 4),
    (b 3)+(b 4),
    0,
    1,
    (b 0),
    (b 1),
    (b 0)+(b 1)+(b 0)*(b 1),
    0,
    (b 3),
    (b 2),
    (b 0)*(b 2)+(b 1)*(b 3),
    (b 2)+(b 0)*(b 3),
    0,
    0,
    0,
    (b 2)*(b 3)+(b 0)*(b 4),
    0,
    (b 2)+(b 1)*(b 3)+(b 0)*(b 2)*(b 3)+(b 1)*(b 4),
    (b 4),
    (b 0)*(b 3)+(b 2)*(b 3)+(b 0)*(b 4)+(b 2)*(b 4)+(b 0)*(b 3)*(b 4),
    0,
    0,
    0,
    0,
    (b 3)+(b 4)+(b 3)*(b 4),
    0 ]

private def state6 (b : Fin 12 → ZMod 2) : Vec :=
  ![(b 3)+(b 4)+(b 0)*(b 5),
    (b 3)+(b 4),
    0,
    1,
    (b 0),
    (b 1),
    (b 0)+(b 1)+(b 0)*(b 1),
    0,
    (b 3),
    (b 2),
    (b 0)*(b 2)+(b 1)*(b 3),
    (b 2)+(b 0)*(b 3),
    0,
    (b 5),
    0,
    (b 2)*(b 3)+(b 0)*(b 4),
    (b 5),
    (b 2)+(b 1)*(b 3)+(b 0)*(b 2)*(b 3)+(b 1)*(b 4)+(b 0)*(b 5)+(b 1)*(b 5)+(b 0)*(b 1)*(b 5),
    (b 4)+(b 2)*(b 5)+(b 0)*(b 3)*(b 5),
    (b 0)*(b 3)+(b 2)*(b 3)+(b 0)*(b 4)+(b 2)*(b 4)+(b 0)*(b 3)*(b 4)+(b 1)*(b 5),
    (b 3)*(b 5),
    0,
    0,
    (b 0)*(b 5)+(b 3)*(b 5)+(b 4)*(b 5),
    (b 3)+(b 4)+(b 3)*(b 4)+(b 2)*(b 5)+(b 2)*(b 3)*(b 5)+(b 0)*(b 4)*(b 5),
    (b 5) ]

private def state7 (b : Fin 12 → ZMod 2) : Vec :=
  ![(b 3)+(b 4)+(b 0)*(b 5),
    (b 3)+(b 4)+(b 2)*(b 6)+(b 0)*(b 3)*(b 6),
    0,
    1,
    (b 0),
    (b 1),
    (b 0)+(b 1)+(b 0)*(b 1),
    (b 6),
    (b 3)+(b 0)*(b 6),
    (b 2)+(b 1)*(b 6),
    (b 0)*(b 2)+(b 1)*(b 3)+(b 0)*(b 6)+(b 1)*(b 6)+(b 0)*(b 1)*(b 6),
    (b 2)+(b 0)*(b 3),
    0,
    (b 5),
    0,
    (b 2)*(b 3)+(b 0)*(b 4),
    (b 5)+(b 3)*(b 6),
    (b 2)+(b 1)*(b 3)+(b 0)*(b 2)*(b 3)+(b 1)*(b 4)+(b 0)*(b 5)+(b 1)*(b 5)+(b 0)*(b 1)*(b 5),
    (b 4)+(b 2)*(b 5)+(b 0)*(b 3)*(b 5)+(b 2)*(b 6),
    (b 0)*(b 3)+(b 2)*(b 3)+(b 0)*(b 4)+(b 2)*(b 4)+(b 0)*(b 3)*(b 4)+(b 1)*(b 5)+(b 0)*(b 2)*(b 6)+(b 1)*(b 3)*(b 6),
    (b 3)*(b 5)+(b 2)*(b 6)+(b 3)*(b 6)+(b 0)*(b 3)*(b 6)+(b 4)*(b 6)+(b 0)*(b 5)*(b 6),
    (b 6),
    (b 0)*(b 6)+(b 3)*(b 6)+(b 5)*(b 6),
    (b 0)*(b 5)+(b 3)*(b 5)+(b 4)*(b 5)+(b 1)*(b 6)+(b 2)*(b 6)+(b 4)*(b 6)+(b 2)*(b 5)*(b 6)+(b 0)*(b 3)*(b 5)*(b 6),
    (b 3)+(b 4)+(b 3)*(b 4)+(b 2)*(b 5)+(b 2)*(b 3)*(b 5)+(b 0)*(b 4)*(b 5)+(b 0)*(b 6)+(b 1)*(b 6)+(b 0)*(b 1)*(b 6)+(b 0)*(b 2)*(b 6)+(b 0)*(b 3)*(b 6)+(b 1)*(b 3)*(b 6)+(b 2)*(b 3)*(b 6)+(b 0)*(b 4)*(b 6)+(b 2)*(b 4)*(b 6)+(b 0)*(b 3)*(b 4)*(b 6)+(b 1)*(b 5)*(b 6),
    (b 5)+(b 2)*(b 6)+(b 0)*(b 3)*(b 6)+(b 3)*(b 5)*(b 6) ]

private def state8 (b : Fin 12 → ZMod 2) : Vec :=
  ![(b 3)+(b 4)+(b 0)*(b 5),
    (b 3)+(b 4)+(b 2)*(b 6)+(b 0)*(b 3)*(b 6),
    0,
    1,
    (b 0),
    (b 1),
    (b 0)+(b 1)+(b 0)*(b 1),
    (b 6),
    (b 3)+(b 0)*(b 6),
    (b 2)+(b 1)*(b 6),
    (b 0)*(b 2)+(b 1)*(b 3)+(b 0)*(b 6)+(b 1)*(b 6)+(b 0)*(b 1)*(b 6),
    (b 2)+(b 0)*(b 3),
    0,
    (b 5),
    (b 7),
    (b 2)*(b 3)+(b 0)*(b 4),
    (b 5)+(b 3)*(b 6)+(b 0)*(b 7),
    (b 2)+(b 1)*(b 3)+(b 0)*(b 2)*(b 3)+(b 1)*(b 4)+(b 0)*(b 5)+(b 1)*(b 5)+(b 0)*(b 1)*(b 5),
    (b 4)+(b 2)*(b 5)+(b 0)*(b 3)*(b 5)+(b 2)*(b 6)+(b 1)*(b 7),
    (b 0)*(b 3)+(b 2)*(b 3)+(b 0)*(b 4)+(b 2)*(b 4)+(b 0)*(b 3)*(b 4)+(b 1)*(b 5)+(b 0)*(b 2)*(b 6)+(b 1)*(b 3)*(b 6)+(b 0)*(b 7)+(b 1)*(b 7)+(b 0)*(b 1)*(b 7),
    (b 3)*(b 5)+(b 2)*(b 6)+(b 3)*(b 6)+(b 0)*(b 3)*(b 6)+(b 4)*(b 6)+(b 0)*(b 5)*(b 6),
    (b 6)+(b 7)+(b 6)*(b 7),
    (b 0)*(b 6)+(b 3)*(b 6)+(b 5)*(b 6)+(b 0)*(b 7)+(b 3)*(b 7)+(b 0)*(b 6)*(b 7),
    (b 0)*(b 5)+(b 3)*(b 5)+(b 4)*(b 5)+(b 1)*(b 6)+(b 2)*(b 6)+(b 4)*(b 6)+(b 2)*(b 5)*(b 6)+(b 0)*(b 3)*(b 5)*(b 6)+(b 1)*(b 7)+(b 2)*(b 7)+(b 1)*(b 6)*(b 7),
    (b 3)+(b 4)+(b 3)*(b 4)+(b 2)*(b 5)+(b 2)*(b 3)*(b 5)+(b 0)*(b 4)*(b 5)+(b 0)*(b 6)+(b 1)*(b 6)+(b 0)*(b 1)*(b 6)+(b 0)*(b 2)*(b 6)+(b 0)*(b 3)*(b 6)+(b 1)*(b 3)*(b 6)+(b 2)*(b 3)*(b 6)+(b 0)*(b 4)*(b 6)+(b 2)*(b 4)*(b 6)+(b 0)*(b 3)*(b 4)*(b 6)+(b 1)*(b 5)*(b 6)+(b 0)*(b 7)+(b 1)*(b 7)+(b 0)*(b 1)*(b 7)+(b 0)*(b 2)*(b 7)+(b 1)*(b 3)*(b 7)+(b 0)*(b 6)*(b 7)+(b 1)*(b 6)*(b 7)+(b 0)*(b 1)*(b 6)*(b 7),
    (b 5)+(b 2)*(b 6)+(b 0)*(b 3)*(b 6)+(b 3)*(b 5)*(b 6)+(b 2)*(b 7)+(b 3)*(b 7)+(b 0)*(b 3)*(b 7)+(b 4)*(b 7)+(b 0)*(b 5)*(b 7) ]

private def state9 (b : Fin 12 → ZMod 2) : Vec :=
  ![(b 3)+(b 4)+(b 0)*(b 5)+(b 1)*(b 8),
    (b 3)+(b 4)+(b 2)*(b 6)+(b 0)*(b 3)*(b 6),
    0,
    1,
    (b 0),
    (b 1),
    (b 0)+(b 1)+(b 0)*(b 1),
    (b 6),
    (b 3)+(b 0)*(b 6),
    (b 2)+(b 1)*(b 6),
    (b 0)*(b 2)+(b 1)*(b 3)+(b 0)*(b 6)+(b 1)*(b 6)+(b 0)*(b 1)*(b 6),
    (b 2)+(b 0)*(b 3),
    (b 8),
    (b 5),
    (b 7)+(b 0)*(b 8),
    (b 2)*(b 3)+(b 0)*(b 4)+(b 0)*(b 8)+(b 1)*(b 8)+(b 0)*(b 1)*(b 8),
    (b 5)+(b 3)*(b 6)+(b 0)*(b 7)+(b 2)*(b 8)+(b 0)*(b 3)*(b 8),
    (b 2)+(b 1)*(b 3)+(b 0)*(b 2)*(b 3)+(b 1)*(b 4)+(b 0)*(b 5)+(b 1)*(b 5)+(b 0)*(b 1)*(b 5),
    (b 4)+(b 2)*(b 5)+(b 0)*(b 3)*(b 5)+(b 2)*(b 6)+(b 1)*(b 7)+(b 0)*(b 8)+(b 1)*(b 8)+(b 0)*(b 1)*(b 8),
    (b 0)*(b 3)+(b 2)*(b 3)+(b 0)*(b 4)+(b 2)*(b 4)+(b 0)*(b 3)*(b 4)+(b 1)*(b 5)+(b 0)*(b 2)*(b 6)+(b 1)*(b 3)*(b 6)+(b 0)*(b 7)+(b 1)*(b 7)+(b 0)*(b 1)*(b 7),
    (b 3)*(b 5)+(b 2)*(b 6)+(b 3)*(b 6)+(b 0)*(b 3)*(b 6)+(b 4)*(b 6)+(b 0)*(b 5)*(b 6)+(b 2)*(b 8)+(b 1)*(b 6)*(b 8),
    (b 6)+(b 7)+(b 6)*(b 7)+(b 3)*(b 8)+(b 5)*(b 8)+(b 0)*(b 6)*(b 8),
    (b 0)*(b 6)+(b 3)*(b 6)+(b 5)*(b 6)+(b 0)*(b 7)+(b 3)*(b 7)+(b 0)*(b 6)*(b 7)+(b 1)*(b 8)+(b 3)*(b 8)+(b 4)*(b 8)+(b 2)*(b 6)*(b 8)+(b 0)*(b 3)*(b 6)*(b 8),
    (b 0)*(b 5)+(b 3)*(b 5)+(b 4)*(b 5)+(b 1)*(b 6)+(b 2)*(b 6)+(b 4)*(b 6)+(b 2)*(b 5)*(b 6)+(b 0)*(b 3)*(b 5)*(b 6)+(b 1)*(b 7)+(b 2)*(b 7)+(b 1)*(b 6)*(b 7)+(b 0)*(b 2)*(b 8)+(b 1)*(b 3)*(b 8)+(b 0)*(b 6)*(b 8)+(b 1)*(b 6)*(b 8)+(b 0)*(b 1)*(b 6)*(b 8),
    (b 3)+(b 4)+(b 3)*(b 4)+(b 2)*(b 5)+(b 2)*(b 3)*(b 5)+(b 0)*(b 4)*(b 5)+(b 0)*(b 6)+(b 1)*(b 6)+(b 0)*(b 1)*(b 6)+(b 0)*(b 2)*(b 6)+(b 0)*(b 3)*(b 6)+(b 1)*(b 3)*(b 6)+(b 2)*(b 3)*(b 6)+(b 0)*(b 4)*(b 6)+(b 2)*(b 4)*(b 6)+(b 0)*(b 3)*(b 4)*(b 6)+(b 1)*(b 5)*(b 6)+(b 0)*(b 7)+(b 1)*(b 7)+(b 0)*(b 1)*(b 7)+(b 0)*(b 2)*(b 7)+(b 1)*(b 3)*(b 7)+(b 0)*(b 6)*(b 7)+(b 1)*(b 6)*(b 7)+(b 0)*(b 1)*(b 6)*(b 7)+(b 2)*(b 8)+(b 1)*(b 3)*(b 8)+(b 0)*(b 2)*(b 3)*(b 8)+(b 1)*(b 4)*(b 8)+(b 0)*(b 5)*(b 8)+(b 1)*(b 5)*(b 8)+(b 0)*(b 1)*(b 5)*(b 8),
    (b 5)+(b 2)*(b 6)+(b 0)*(b 3)*(b 6)+(b 3)*(b 5)*(b 6)+(b 2)*(b 7)+(b 3)*(b 7)+(b 0)*(b 3)*(b 7)+(b 4)*(b 7)+(b 0)*(b 5)*(b 7)+(b 0)*(b 8)+(b 1)*(b 8)+(b 0)*(b 1)*(b 8)+(b 2)*(b 3)*(b 8)+(b 4)*(b 8)+(b 0)*(b 4)*(b 8)+(b 2)*(b 5)*(b 8)+(b 0)*(b 3)*(b 5)*(b 8)+(b 2)*(b 6)*(b 8)+(b 1)*(b 7)*(b 8) ]

private def state10 (b : Fin 12 → ZMod 2) : Vec :=
  ![(b 3)+(b 4)+(b 0)*(b 5)+(b 1)*(b 8)+(b 0)*(b 9)+(b 1)*(b 9)+(b 0)*(b 1)*(b 9)+(b 2)*(b 9)+(b 1)*(b 6)*(b 9),
    (b 3)+(b 4)+(b 2)*(b 6)+(b 0)*(b 3)*(b 6)+(b 0)*(b 9)+(b 1)*(b 9)+(b 0)*(b 1)*(b 9)+(b 2)*(b 9)+(b 1)*(b 6)*(b 9),
    0,
    1,
    (b 0),
    (b 1),
    (b 0)+(b 1)+(b 0)*(b 1),
    (b 6)+(b 0)*(b 9),
    (b 3)+(b 0)*(b 6),
    (b 2)+(b 1)*(b 6)+(b 0)*(b 9)+(b 1)*(b 9)+(b 0)*(b 1)*(b 9),
    (b 0)*(b 2)+(b 1)*(b 3)+(b 0)*(b 6)+(b 1)*(b 6)+(b 0)*(b 1)*(b 6),
    (b 2)+(b 0)*(b 3)+(b 1)*(b 9),
    (b 8)+(b 0)*(b 9)+(b 6)*(b 9),
    (b 5)+(b 2)*(b 9)+(b 0)*(b 3)*(b 9),
    (b 7)+(b 0)*(b 8)+(b 1)*(b 9)+(b 2)*(b 9)+(b 0)*(b 3)*(b 9)+(b 5)*(b 9),
    (b 2)*(b 3)+(b 0)*(b 4)+(b 0)*(b 8)+(b 1)*(b 8)+(b 0)*(b 1)*(b 8)+(b 0)*(b 2)*(b 9)+(b 1)*(b 3)*(b 9)+(b 0)*(b 6)*(b 9)+(b 1)*(b 6)*(b 9)+(b 0)*(b 1)*(b 6)*(b 9),
    (b 5)+(b 3)*(b 6)+(b 0)*(b 7)+(b 2)*(b 8)+(b 0)*(b 3)*(b 8)+(b 2)*(b 9)+(b 0)*(b 5)*(b 9)+(b 1)*(b 6)*(b 9)+(b 2)*(b 6)*(b 9)+(b 0)*(b 3)*(b 6)*(b 9)+(b 1)*(b 8)*(b 9),
    (b 2)+(b 1)*(b 3)+(b 0)*(b 2)*(b 3)+(b 1)*(b 4)+(b 0)*(b 5)+(b 1)*(b 5)+(b 0)*(b 1)*(b 5),
    (b 4)+(b 2)*(b 5)+(b 0)*(b 3)*(b 5)+(b 2)*(b 6)+(b 1)*(b 7)+(b 0)*(b 8)+(b 1)*(b 8)+(b 0)*(b 1)*(b 8),
    (b 0)*(b 3)+(b 2)*(b 3)+(b 0)*(b 4)+(b 2)*(b 4)+(b 0)*(b 3)*(b 4)+(b 1)*(b 5)+(b 0)*(b 2)*(b 6)+(b 1)*(b 3)*(b 6)+(b 0)*(b 7)+(b 1)*(b 7)+(b 0)*(b 1)*(b 7)+(b 2)*(b 9)+(b 1)*(b 3)*(b 9)+(b 0)*(b 2)*(b 3)*(b 9)+(b 1)*(b 4)*(b 9)+(b 0)*(b 5)*(b 9)+(b 1)*(b 5)*(b 9)+(b 0)*(b 1)*(b 5)*(b 9),
    (b 3)*(b 5)+(b 2)*(b 6)+(b 3)*(b 6)+(b 0)*(b 3)*(b 6)+(b 4)*(b 6)+(b 0)*(b 5)*(b 6)+(b 2)*(b 8)+(b 1)*(b 6)*(b 8)+(b 2)*(b 3)*(b 9)+(b 0)*(b 4)*(b 9)+(b 0)*(b 8)*(b 9)+(b 1)*(b 8)*(b 9)+(b 0)*(b 1)*(b 8)*(b 9),
    (b 6)+(b 7)+(b 6)*(b 7)+(b 3)*(b 8)+(b 5)*(b 8)+(b 0)*(b 6)*(b 8)+(b 0)*(b 9)+(b 1)*(b 9)+(b 0)*(b 1)*(b 9)+(b 2)*(b 9)+(b 5)*(b 9)+(b 1)*(b 6)*(b 9)+(b 3)*(b 6)*(b 9)+(b 0)*(b 7)*(b 9)+(b 2)*(b 8)*(b 9)+(b 0)*(b 3)*(b 8)*(b 9),
    (b 0)*(b 6)+(b 3)*(b 6)+(b 5)*(b 6)+(b 0)*(b 7)+(b 3)*(b 7)+(b 0)*(b 6)*(b 7)+(b 1)*(b 8)+(b 3)*(b 8)+(b 4)*(b 8)+(b 2)*(b 6)*(b 8)+(b 0)*(b 3)*(b 6)*(b 8)+(b 0)*(b 2)*(b 9)+(b 1)*(b 3)*(b 9)+(b 2)*(b 3)*(b 9)+(b 0)*(b 4)*(b 9)+(b 3)*(b 5)*(b 9)+(b 0)*(b 6)*(b 9)+(b 1)*(b 6)*(b 9)+(b 0)*(b 1)*(b 6)*(b 9)+(b 2)*(b 6)*(b 9)+(b 3)*(b 6)*(b 9)+(b 0)*(b 3)*(b 6)*(b 9)+(b 4)*(b 6)*(b 9)+(b 0)*(b 5)*(b 6)*(b 9)+(b 0)*(b 8)*(b 9)+(b 1)*(b 8)*(b 9)+(b 0)*(b 1)*(b 8)*(b 9)+(b 2)*(b 8)*(b 9)+(b 1)*(b 6)*(b 8)*(b 9),
    (b 0)*(b 5)+(b 3)*(b 5)+(b 4)*(b 5)+(b 1)*(b 6)+(b 2)*(b 6)+(b 4)*(b 6)+(b 2)*(b 5)*(b 6)+(b 0)*(b 3)*(b 5)*(b 6)+(b 1)*(b 7)+(b 2)*(b 7)+(b 1)*(b 6)*(b 7)+(b 0)*(b 2)*(b 8)+(b 1)*(b 3)*(b 8)+(b 0)*(b 6)*(b 8)+(b 1)*(b 6)*(b 8)+(b 0)*(b 1)*(b 6)*(b 8)+(b 0)*(b 3)*(b 9)+(b 2)*(b 3)*(b 9)+(b 0)*(b 4)*(b 9)+(b 2)*(b 4)*(b 9)+(b 0)*(b 3)*(b 4)*(b 9)+(b 1)*(b 5)*(b 9)+(b 0)*(b 2)*(b 6)*(b 9)+(b 1)*(b 3)*(b 6)*(b 9)+(b 0)*(b 7)*(b 9)+(b 1)*(b 7)*(b 9)+(b 0)*(b 1)*(b 7)*(b 9),
    (b 3)+(b 4)+(b 3)*(b 4)+(b 2)*(b 5)+(b 2)*(b 3)*(b 5)+(b 0)*(b 4)*(b 5)+(b 0)*(b 6)+(b 1)*(b 6)+(b 0)*(b 1)*(b 6)+(b 0)*(b 2)*(b 6)+(b 0)*(b 3)*(b 6)+(b 1)*(b 3)*(b 6)+(b 2)*(b 3)*(b 6)+(b 0)*(b 4)*(b 6)+(b 2)*(b 4)*(b 6)+(b 0)*(b 3)*(b 4)*(b 6)+(b 1)*(b 5)*(b 6)+(b 0)*(b 7)+(b 1)*(b 7)+(b 0)*(b 1)*(b 7)+(b 0)*(b 2)*(b 7)+(b 1)*(b 3)*(b 7)+(b 0)*(b 6)*(b 7)+(b 1)*(b 6)*(b 7)+(b 0)*(b 1)*(b 6)*(b 7)+(b 2)*(b 8)+(b 1)*(b 3)*(b 8)+(b 0)*(b 2)*(b 3)*(b 8)+(b 1)*(b 4)*(b 8)+(b 0)*(b 5)*(b 8)+(b 1)*(b 5)*(b 8)+(b 0)*(b 1)*(b 5)*(b 8),
    (b 5)+(b 2)*(b 6)+(b 0)*(b 3)*(b 6)+(b 3)*(b 5)*(b 6)+(b 2)*(b 7)+(b 3)*(b 7)+(b 0)*(b 3)*(b 7)+(b 4)*(b 7)+(b 0)*(b 5)*(b 7)+(b 0)*(b 8)+(b 1)*(b 8)+(b 0)*(b 1)*(b 8)+(b 2)*(b 3)*(b 8)+(b 4)*(b 8)+(b 0)*(b 4)*(b 8)+(b 2)*(b 5)*(b 8)+(b 0)*(b 3)*(b 5)*(b 8)+(b 2)*(b 6)*(b 8)+(b 1)*(b 7)*(b 8)+(b 2)*(b 9)+(b 0)*(b 3)*(b 9)+(b 1)*(b 3)*(b 9)+(b 2)*(b 3)*(b 9)+(b 0)*(b 2)*(b 3)*(b 9)+(b 0)*(b 4)*(b 9)+(b 1)*(b 4)*(b 9)+(b 2)*(b 4)*(b 9)+(b 0)*(b 3)*(b 4)*(b 9)+(b 0)*(b 1)*(b 5)*(b 9)+(b 3)*(b 5)*(b 9)+(b 4)*(b 5)*(b 9)+(b 1)*(b 6)*(b 9)+(b 2)*(b 6)*(b 9)+(b 0)*(b 2)*(b 6)*(b 9)+(b 1)*(b 3)*(b 6)*(b 9)+(b 4)*(b 6)*(b 9)+(b 2)*(b 5)*(b 6)*(b 9)+(b 0)*(b 3)*(b 5)*(b 6)*(b 9)+(b 0)*(b 7)*(b 9)+(b 0)*(b 1)*(b 7)*(b 9)+(b 2)*(b 7)*(b 9)+(b 1)*(b 6)*(b 7)*(b 9)+(b 0)*(b 2)*(b 8)*(b 9)+(b 1)*(b 3)*(b 8)*(b 9)+(b 0)*(b 6)*(b 8)*(b 9)+(b 1)*(b 6)*(b 8)*(b 9)+(b 0)*(b 1)*(b 6)*(b 8)*(b 9) ]

private def state11 (b : Fin 12 → ZMod 2) : Vec :=
  ![(b 3)+(b 4)+(b 0)*(b 5)+(b 1)*(b 8)+(b 0)*(b 9)+(b 1)*(b 9)+(b 0)*(b 1)*(b 9)+(b 2)*(b 9)+(b 1)*(b 6)*(b 9)+(b 0)*(b 10)+(b 1)*(b 10)+(b 0)*(b 1)*(b 10),
    (b 3)+(b 4)+(b 2)*(b 6)+(b 0)*(b 3)*(b 6)+(b 0)*(b 9)+(b 1)*(b 9)+(b 0)*(b 1)*(b 9)+(b 2)*(b 9)+(b 1)*(b 6)*(b 9)+(b 0)*(b 10)+(b 1)*(b 10)+(b 0)*(b 1)*(b 10),
    0,
    1,
    (b 0),
    (b 1),
    (b 0)+(b 1)+(b 0)*(b 1),
    (b 6)+(b 0)*(b 9),
    (b 3)+(b 0)*(b 6),
    (b 2)+(b 1)*(b 6)+(b 0)*(b 9)+(b 1)*(b 9)+(b 0)*(b 1)*(b 9),
    (b 0)*(b 2)+(b 1)*(b 3)+(b 0)*(b 6)+(b 1)*(b 6)+(b 0)*(b 1)*(b 6),
    (b 2)+(b 0)*(b 3)+(b 1)*(b 9),
    (b 8)+(b 0)*(b 9)+(b 6)*(b 9)+(b 0)*(b 10),
    (b 5)+(b 2)*(b 9)+(b 0)*(b 3)*(b 9)+(b 1)*(b 10),
    (b 7)+(b 0)*(b 8)+(b 1)*(b 9)+(b 2)*(b 9)+(b 0)*(b 3)*(b 9)+(b 5)*(b 9)+(b 1)*(b 10)+(b 2)*(b 10)+(b 0)*(b 3)*(b 10)+(b 1)*(b 9)*(b 10),
    (b 2)*(b 3)+(b 0)*(b 4)+(b 0)*(b 8)+(b 1)*(b 8)+(b 0)*(b 1)*(b 8)+(b 0)*(b 2)*(b 9)+(b 1)*(b 3)*(b 9)+(b 0)*(b 6)*(b 9)+(b 1)*(b 6)*(b 9)+(b 0)*(b 1)*(b 6)*(b 9),
    (b 5)+(b 3)*(b 6)+(b 0)*(b 7)+(b 2)*(b 8)+(b 0)*(b 3)*(b 8)+(b 2)*(b 9)+(b 0)*(b 5)*(b 9)+(b 1)*(b 6)*(b 9)+(b 2)*(b 6)*(b 9)+(b 0)*(b 3)*(b 6)*(b 9)+(b 1)*(b 8)*(b 9)+(b 0)*(b 10)+(b 1)*(b 10)+(b 0)*(b 1)*(b 10),
    (b 2)+(b 1)*(b 3)+(b 0)*(b 2)*(b 3)+(b 1)*(b 4)+(b 0)*(b 5)+(b 1)*(b 5)+(b 0)*(b 1)*(b 5),
    (b 4)+(b 2)*(b 5)+(b 0)*(b 3)*(b 5)+(b 2)*(b 6)+(b 1)*(b 7)+(b 0)*(b 8)+(b 1)*(b 8)+(b 0)*(b 1)*(b 8),
    (b 0)*(b 3)+(b 2)*(b 3)+(b 0)*(b 4)+(b 2)*(b 4)+(b 0)*(b 3)*(b 4)+(b 1)*(b 5)+(b 0)*(b 2)*(b 6)+(b 1)*(b 3)*(b 6)+(b 0)*(b 7)+(b 1)*(b 7)+(b 0)*(b 1)*(b 7)+(b 2)*(b 9)+(b 1)*(b 3)*(b 9)+(b 0)*(b 2)*(b 3)*(b 9)+(b 1)*(b 4)*(b 9)+(b 0)*(b 5)*(b 9)+(b 1)*(b 5)*(b 9)+(b 0)*(b 1)*(b 5)*(b 9),
    (b 3)*(b 5)+(b 2)*(b 6)+(b 3)*(b 6)+(b 0)*(b 3)*(b 6)+(b 4)*(b 6)+(b 0)*(b 5)*(b 6)+(b 2)*(b 8)+(b 1)*(b 6)*(b 8)+(b 2)*(b 3)*(b 9)+(b 0)*(b 4)*(b 9)+(b 0)*(b 8)*(b 9)+(b 1)*(b 8)*(b 9)+(b 0)*(b 1)*(b 8)*(b 9)+(b 0)*(b 2)*(b 10)+(b 1)*(b 3)*(b 10)+(b 0)*(b 6)*(b 10)+(b 1)*(b 6)*(b 10)+(b 0)*(b 1)*(b 6)*(b 10),
    (b 6)+(b 7)+(b 6)*(b 7)+(b 3)*(b 8)+(b 5)*(b 8)+(b 0)*(b 6)*(b 8)+(b 0)*(b 9)+(b 1)*(b 9)+(b 0)*(b 1)*(b 9)+(b 2)*(b 9)+(b 5)*(b 9)+(b 1)*(b 6)*(b 9)+(b 3)*(b 6)*(b 9)+(b 0)*(b 7)*(b 9)+(b 2)*(b 8)*(b 9)+(b 0)*(b 3)*(b 8)*(b 9)+(b 0)*(b 10)+(b 1)*(b 10)+(b 0)*(b 1)*(b 10)+(b 2)*(b 10)+(b 0)*(b 5)*(b 10)+(b 1)*(b 6)*(b 10)+(b 2)*(b 6)*(b 10)+(b 0)*(b 3)*(b 6)*(b 10)+(b 1)*(b 8)*(b 10)+(b 0)*(b 9)*(b 10)+(b 1)*(b 9)*(b 10)+(b 0)*(b 1)*(b 9)*(b 10),
    (b 0)*(b 6)+(b 3)*(b 6)+(b 5)*(b 6)+(b 0)*(b 7)+(b 3)*(b 7)+(b 0)*(b 6)*(b 7)+(b 1)*(b 8)+(b 3)*(b 8)+(b 4)*(b 8)+(b 2)*(b 6)*(b 8)+(b 0)*(b 3)*(b 6)*(b 8)+(b 0)*(b 2)*(b 9)+(b 1)*(b 3)*(b 9)+(b 2)*(b 3)*(b 9)+(b 0)*(b 4)*(b 9)+(b 3)*(b 5)*(b 9)+(b 0)*(b 6)*(b 9)+(b 1)*(b 6)*(b 9)+(b 0)*(b 1)*(b 6)*(b 9)+(b 2)*(b 6)*(b 9)+(b 3)*(b 6)*(b 9)+(b 0)*(b 3)*(b 6)*(b 9)+(b 4)*(b 6)*(b 9)+(b 0)*(b 5)*(b 6)*(b 9)+(b 0)*(b 8)*(b 9)+(b 1)*(b 8)*(b 9)+(b 0)*(b 1)*(b 8)*(b 9)+(b 2)*(b 8)*(b 9)+(b 1)*(b 6)*(b 8)*(b 9)+(b 0)*(b 2)*(b 10)+(b 1)*(b 3)*(b 10)+(b 2)*(b 3)*(b 10)+(b 0)*(b 4)*(b 10)+(b 0)*(b 6)*(b 10)+(b 1)*(b 6)*(b 10)+(b 0)*(b 1)*(b 6)*(b 10)+(b 0)*(b 8)*(b 10)+(b 1)*(b 8)*(b 10)+(b 0)*(b 1)*(b 8)*(b 10)+(b 0)*(b 2)*(b 9)*(b 10)+(b 1)*(b 3)*(b 9)*(b 10)+(b 0)*(b 6)*(b 9)*(b 10)+(b 1)*(b 6)*(b 9)*(b 10)+(b 0)*(b 1)*(b 6)*(b 9)*(b 10),
    (b 0)*(b 5)+(b 3)*(b 5)+(b 4)*(b 5)+(b 1)*(b 6)+(b 2)*(b 6)+(b 4)*(b 6)+(b 2)*(b 5)*(b 6)+(b 0)*(b 3)*(b 5)*(b 6)+(b 1)*(b 7)+(b 2)*(b 7)+(b 1)*(b 6)*(b 7)+(b 0)*(b 2)*(b 8)+(b 1)*(b 3)*(b 8)+(b 0)*(b 6)*(b 8)+(b 1)*(b 6)*(b 8)+(b 0)*(b 1)*(b 6)*(b 8)+(b 0)*(b 3)*(b 9)+(b 2)*(b 3)*(b 9)+(b 0)*(b 4)*(b 9)+(b 2)*(b 4)*(b 9)+(b 0)*(b 3)*(b 4)*(b 9)+(b 1)*(b 5)*(b 9)+(b 0)*(b 2)*(b 6)*(b 9)+(b 1)*(b 3)*(b 6)*(b 9)+(b 0)*(b 7)*(b 9)+(b 1)*(b 7)*(b 9)+(b 0)*(b 1)*(b 7)*(b 9)+(b 2)*(b 10)+(b 1)*(b 3)*(b 10)+(b 0)*(b 2)*(b 3)*(b 10)+(b 1)*(b 4)*(b 10)+(b 0)*(b 5)*(b 10)+(b 1)*(b 5)*(b 10)+(b 0)*(b 1)*(b 5)*(b 10),
    (b 3)+(b 4)+(b 3)*(b 4)+(b 2)*(b 5)+(b 2)*(b 3)*(b 5)+(b 0)*(b 4)*(b 5)+(b 0)*(b 6)+(b 1)*(b 6)+(b 0)*(b 1)*(b 6)+(b 0)*(b 2)*(b 6)+(b 0)*(b 3)*(b 6)+(b 1)*(b 3)*(b 6)+(b 2)*(b 3)*(b 6)+(b 0)*(b 4)*(b 6)+(b 2)*(b 4)*(b 6)+(b 0)*(b 3)*(b 4)*(b 6)+(b 1)*(b 5)*(b 6)+(b 0)*(b 7)+(b 1)*(b 7)+(b 0)*(b 1)*(b 7)+(b 0)*(b 2)*(b 7)+(b 1)*(b 3)*(b 7)+(b 0)*(b 6)*(b 7)+(b 1)*(b 6)*(b 7)+(b 0)*(b 1)*(b 6)*(b 7)+(b 2)*(b 8)+(b 1)*(b 3)*(b 8)+(b 0)*(b 2)*(b 3)*(b 8)+(b 1)*(b 4)*(b 8)+(b 0)*(b 5)*(b 8)+(b 1)*(b 5)*(b 8)+(b 0)*(b 1)*(b 5)*(b 8),
    (b 5)+(b 2)*(b 6)+(b 0)*(b 3)*(b 6)+(b 3)*(b 5)*(b 6)+(b 2)*(b 7)+(b 3)*(b 7)+(b 0)*(b 3)*(b 7)+(b 4)*(b 7)+(b 0)*(b 5)*(b 7)+(b 0)*(b 8)+(b 1)*(b 8)+(b 0)*(b 1)*(b 8)+(b 2)*(b 3)*(b 8)+(b 4)*(b 8)+(b 0)*(b 4)*(b 8)+(b 2)*(b 5)*(b 8)+(b 0)*(b 3)*(b 5)*(b 8)+(b 2)*(b 6)*(b 8)+(b 1)*(b 7)*(b 8)+(b 2)*(b 9)+(b 0)*(b 3)*(b 9)+(b 1)*(b 3)*(b 9)+(b 2)*(b 3)*(b 9)+(b 0)*(b 2)*(b 3)*(b 9)+(b 0)*(b 4)*(b 9)+(b 1)*(b 4)*(b 9)+(b 2)*(b 4)*(b 9)+(b 0)*(b 3)*(b 4)*(b 9)+(b 0)*(b 1)*(b 5)*(b 9)+(b 3)*(b 5)*(b 9)+(b 4)*(b 5)*(b 9)+(b 1)*(b 6)*(b 9)+(b 2)*(b 6)*(b 9)+(b 0)*(b 2)*(b 6)*(b 9)+(b 1)*(b 3)*(b 6)*(b 9)+(b 4)*(b 6)*(b 9)+(b 2)*(b 5)*(b 6)*(b 9)+(b 0)*(b 3)*(b 5)*(b 6)*(b 9)+(b 0)*(b 7)*(b 9)+(b 0)*(b 1)*(b 7)*(b 9)+(b 2)*(b 7)*(b 9)+(b 1)*(b 6)*(b 7)*(b 9)+(b 0)*(b 2)*(b 8)*(b 9)+(b 1)*(b 3)*(b 8)*(b 9)+(b 0)*(b 6)*(b 8)*(b 9)+(b 1)*(b 6)*(b 8)*(b 9)+(b 0)*(b 1)*(b 6)*(b 8)*(b 9)+(b 2)*(b 10)+(b 0)*(b 3)*(b 10)+(b 1)*(b 3)*(b 10)+(b 2)*(b 3)*(b 10)+(b 0)*(b 2)*(b 3)*(b 10)+(b 0)*(b 4)*(b 10)+(b 1)*(b 4)*(b 10)+(b 2)*(b 4)*(b 10)+(b 0)*(b 3)*(b 4)*(b 10)+(b 0)*(b 5)*(b 10)+(b 0)*(b 1)*(b 5)*(b 10)+(b 0)*(b 2)*(b 6)*(b 10)+(b 1)*(b 3)*(b 6)*(b 10)+(b 0)*(b 7)*(b 10)+(b 1)*(b 7)*(b 10)+(b 0)*(b 1)*(b 7)*(b 10)+(b 2)*(b 9)*(b 10)+(b 1)*(b 3)*(b 9)*(b 10)+(b 0)*(b 2)*(b 3)*(b 9)*(b 10)+(b 1)*(b 4)*(b 9)*(b 10)+(b 0)*(b 5)*(b 9)*(b 10)+(b 1)*(b 5)*(b 9)*(b 10)+(b 0)*(b 1)*(b 5)*(b 9)*(b 10) ]

def columnThree (b : Fin 12 → ZMod 2) : Vec :=
  ![(b 3)+(b 4)+(b 0)*(b 5)+(b 1)*(b 8)+(b 0)*(b 9)+(b 1)*(b 9)+(b 0)*(b 1)*(b 9)+(b 2)*(b 9)+(b 1)*(b 6)*(b 9)+(b 0)*(b 10)+(b 1)*(b 10)+(b 0)*(b 1)*(b 10)+(b 0)*(b 2)*(b 11)+(b 1)*(b 3)*(b 11)+(b 0)*(b 6)*(b 11)+(b 1)*(b 6)*(b 11)+(b 0)*(b 1)*(b 6)*(b 11),
    (b 3)+(b 4)+(b 2)*(b 6)+(b 0)*(b 3)*(b 6)+(b 0)*(b 9)+(b 1)*(b 9)+(b 0)*(b 1)*(b 9)+(b 2)*(b 9)+(b 1)*(b 6)*(b 9)+(b 0)*(b 10)+(b 1)*(b 10)+(b 0)*(b 1)*(b 10),
    0,
    1,
    (b 0),
    (b 1),
    (b 0)+(b 1)+(b 0)*(b 1),
    (b 6)+(b 0)*(b 9)+(b 1)*(b 11),
    (b 3)+(b 0)*(b 6)+(b 0)*(b 11)+(b 1)*(b 11)+(b 0)*(b 1)*(b 11),
    (b 2)+(b 1)*(b 6)+(b 0)*(b 9)+(b 1)*(b 9)+(b 0)*(b 1)*(b 9),
    (b 0)*(b 2)+(b 1)*(b 3)+(b 0)*(b 6)+(b 1)*(b 6)+(b 0)*(b 1)*(b 6),
    (b 2)+(b 0)*(b 3)+(b 1)*(b 9)+(b 0)*(b 11)+(b 1)*(b 11)+(b 0)*(b 1)*(b 11),
    (b 8)+(b 0)*(b 9)+(b 6)*(b 9)+(b 0)*(b 10)+(b 0)*(b 11)+(b 1)*(b 11)+(b 0)*(b 1)*(b 11)+(b 2)*(b 11)+(b 3)*(b 11)+(b 0)*(b 3)*(b 11)+(b 0)*(b 6)*(b 11)+(b 1)*(b 9)*(b 11),
    (b 5)+(b 2)*(b 9)+(b 0)*(b 3)*(b 9)+(b 1)*(b 10)+(b 2)*(b 11)+(b 1)*(b 6)*(b 11)+(b 0)*(b 9)*(b 11)+(b 1)*(b 9)*(b 11)+(b 0)*(b 1)*(b 9)*(b 11),
    (b 7)+(b 0)*(b 8)+(b 1)*(b 9)+(b 2)*(b 9)+(b 0)*(b 3)*(b 9)+(b 5)*(b 9)+(b 1)*(b 10)+(b 2)*(b 10)+(b 0)*(b 3)*(b 10)+(b 1)*(b 9)*(b 10)+(b 0)*(b 2)*(b 11)+(b 3)*(b 11)+(b 1)*(b 3)*(b 11)+(b 4)*(b 11)+(b 0)*(b 6)*(b 11)+(b 1)*(b 6)*(b 11)+(b 0)*(b 1)*(b 6)*(b 11)+(b 2)*(b 6)*(b 11)+(b 0)*(b 3)*(b 6)*(b 11)+(b 0)*(b 9)*(b 11)+(b 1)*(b 9)*(b 11)+(b 0)*(b 1)*(b 9)*(b 11)+(b 2)*(b 9)*(b 11)+(b 1)*(b 6)*(b 9)*(b 11)+(b 0)*(b 10)*(b 11)+(b 1)*(b 10)*(b 11)+(b 0)*(b 1)*(b 10)*(b 11),
    (b 2)*(b 3)+(b 0)*(b 4)+(b 0)*(b 8)+(b 1)*(b 8)+(b 0)*(b 1)*(b 8)+(b 0)*(b 2)*(b 9)+(b 1)*(b 3)*(b 9)+(b 0)*(b 6)*(b 9)+(b 1)*(b 6)*(b 9)+(b 0)*(b 1)*(b 6)*(b 9),
    (b 5)+(b 3)*(b 6)+(b 0)*(b 7)+(b 2)*(b 8)+(b 0)*(b 3)*(b 8)+(b 2)*(b 9)+(b 0)*(b 5)*(b 9)+(b 1)*(b 6)*(b 9)+(b 2)*(b 6)*(b 9)+(b 0)*(b 3)*(b 6)*(b 9)+(b 1)*(b 8)*(b 9)+(b 0)*(b 10)+(b 1)*(b 10)+(b 0)*(b 1)*(b 10)+(b 2)*(b 3)*(b 11)+(b 0)*(b 4)*(b 11)+(b 0)*(b 8)*(b 11)+(b 1)*(b 8)*(b 11)+(b 0)*(b 1)*(b 8)*(b 11)+(b 0)*(b 2)*(b 9)*(b 11)+(b 1)*(b 3)*(b 9)*(b 11)+(b 0)*(b 6)*(b 9)*(b 11)+(b 1)*(b 6)*(b 9)*(b 11)+(b 0)*(b 1)*(b 6)*(b 9)*(b 11),
    (b 2)+(b 1)*(b 3)+(b 0)*(b 2)*(b 3)+(b 1)*(b 4)+(b 0)*(b 5)+(b 1)*(b 5)+(b 0)*(b 1)*(b 5),
    (b 4)+(b 2)*(b 5)+(b 0)*(b 3)*(b 5)+(b 2)*(b 6)+(b 1)*(b 7)+(b 0)*(b 8)+(b 1)*(b 8)+(b 0)*(b 1)*(b 8)+(b 2)*(b 11)+(b 1)*(b 3)*(b 11)+(b 0)*(b 2)*(b 3)*(b 11)+(b 1)*(b 4)*(b 11)+(b 0)*(b 5)*(b 11)+(b 1)*(b 5)*(b 11)+(b 0)*(b 1)*(b 5)*(b 11),
    (b 0)*(b 3)+(b 2)*(b 3)+(b 0)*(b 4)+(b 2)*(b 4)+(b 0)*(b 3)*(b 4)+(b 1)*(b 5)+(b 0)*(b 2)*(b 6)+(b 1)*(b 3)*(b 6)+(b 0)*(b 7)+(b 1)*(b 7)+(b 0)*(b 1)*(b 7)+(b 2)*(b 9)+(b 1)*(b 3)*(b 9)+(b 0)*(b 2)*(b 3)*(b 9)+(b 1)*(b 4)*(b 9)+(b 0)*(b 5)*(b 9)+(b 1)*(b 5)*(b 9)+(b 0)*(b 1)*(b 5)*(b 9),
    (b 3)*(b 5)+(b 2)*(b 6)+(b 3)*(b 6)+(b 0)*(b 3)*(b 6)+(b 4)*(b 6)+(b 0)*(b 5)*(b 6)+(b 2)*(b 8)+(b 1)*(b 6)*(b 8)+(b 2)*(b 3)*(b 9)+(b 0)*(b 4)*(b 9)+(b 0)*(b 8)*(b 9)+(b 1)*(b 8)*(b 9)+(b 0)*(b 1)*(b 8)*(b 9)+(b 0)*(b 2)*(b 10)+(b 1)*(b 3)*(b 10)+(b 0)*(b 6)*(b 10)+(b 1)*(b 6)*(b 10)+(b 0)*(b 1)*(b 6)*(b 10)+(b 2)*(b 11)+(b 1)*(b 3)*(b 11)+(b 0)*(b 2)*(b 3)*(b 11)+(b 1)*(b 4)*(b 11)+(b 0)*(b 5)*(b 11)+(b 1)*(b 5)*(b 11)+(b 0)*(b 1)*(b 5)*(b 11),
    (b 6)+(b 7)+(b 6)*(b 7)+(b 3)*(b 8)+(b 5)*(b 8)+(b 0)*(b 6)*(b 8)+(b 0)*(b 9)+(b 1)*(b 9)+(b 0)*(b 1)*(b 9)+(b 2)*(b 9)+(b 5)*(b 9)+(b 1)*(b 6)*(b 9)+(b 3)*(b 6)*(b 9)+(b 0)*(b 7)*(b 9)+(b 2)*(b 8)*(b 9)+(b 0)*(b 3)*(b 8)*(b 9)+(b 0)*(b 10)+(b 1)*(b 10)+(b 0)*(b 1)*(b 10)+(b 2)*(b 10)+(b 0)*(b 5)*(b 10)+(b 1)*(b 6)*(b 10)+(b 2)*(b 6)*(b 10)+(b 0)*(b 3)*(b 6)*(b 10)+(b 1)*(b 8)*(b 10)+(b 0)*(b 9)*(b 10)+(b 1)*(b 9)*(b 10)+(b 0)*(b 1)*(b 9)*(b 10)+(b 2)*(b 11)+(b 1)*(b 3)*(b 11)+(b 0)*(b 2)*(b 3)*(b 11)+(b 4)*(b 11)+(b 1)*(b 4)*(b 11)+(b 0)*(b 5)*(b 11)+(b 1)*(b 5)*(b 11)+(b 0)*(b 1)*(b 5)*(b 11)+(b 2)*(b 5)*(b 11)+(b 3)*(b 5)*(b 11)+(b 0)*(b 3)*(b 5)*(b 11)+(b 3)*(b 6)*(b 11)+(b 0)*(b 3)*(b 6)*(b 11)+(b 4)*(b 6)*(b 11)+(b 0)*(b 5)*(b 6)*(b 11)+(b 1)*(b 7)*(b 11)+(b 0)*(b 8)*(b 11)+(b 1)*(b 8)*(b 11)+(b 0)*(b 1)*(b 8)*(b 11)+(b 2)*(b 8)*(b 11)+(b 1)*(b 6)*(b 8)*(b 11)+(b 2)*(b 3)*(b 9)*(b 11)+(b 0)*(b 4)*(b 9)*(b 11)+(b 0)*(b 8)*(b 9)*(b 11)+(b 1)*(b 8)*(b 9)*(b 11)+(b 0)*(b 1)*(b 8)*(b 9)*(b 11)+(b 0)*(b 2)*(b 10)*(b 11)+(b 1)*(b 3)*(b 10)*(b 11)+(b 0)*(b 6)*(b 10)*(b 11)+(b 1)*(b 6)*(b 10)*(b 11)+(b 0)*(b 1)*(b 6)*(b 10)*(b 11),
    (b 0)*(b 6)+(b 3)*(b 6)+(b 5)*(b 6)+(b 0)*(b 7)+(b 3)*(b 7)+(b 0)*(b 6)*(b 7)+(b 1)*(b 8)+(b 3)*(b 8)+(b 4)*(b 8)+(b 2)*(b 6)*(b 8)+(b 0)*(b 3)*(b 6)*(b 8)+(b 0)*(b 2)*(b 9)+(b 1)*(b 3)*(b 9)+(b 2)*(b 3)*(b 9)+(b 0)*(b 4)*(b 9)+(b 3)*(b 5)*(b 9)+(b 0)*(b 6)*(b 9)+(b 1)*(b 6)*(b 9)+(b 0)*(b 1)*(b 6)*(b 9)+(b 2)*(b 6)*(b 9)+(b 3)*(b 6)*(b 9)+(b 0)*(b 3)*(b 6)*(b 9)+(b 4)*(b 6)*(b 9)+(b 0)*(b 5)*(b 6)*(b 9)+(b 0)*(b 8)*(b 9)+(b 1)*(b 8)*(b 9)+(b 0)*(b 1)*(b 8)*(b 9)+(b 2)*(b 8)*(b 9)+(b 1)*(b 6)*(b 8)*(b 9)+(b 0)*(b 2)*(b 10)+(b 1)*(b 3)*(b 10)+(b 2)*(b 3)*(b 10)+(b 0)*(b 4)*(b 10)+(b 0)*(b 6)*(b 10)+(b 1)*(b 6)*(b 10)+(b 0)*(b 1)*(b 6)*(b 10)+(b 0)*(b 8)*(b 10)+(b 1)*(b 8)*(b 10)+(b 0)*(b 1)*(b 8)*(b 10)+(b 0)*(b 2)*(b 9)*(b 10)+(b 1)*(b 3)*(b 9)*(b 10)+(b 0)*(b 6)*(b 9)*(b 10)+(b 1)*(b 6)*(b 9)*(b 10)+(b 0)*(b 1)*(b 6)*(b 9)*(b 10)+(b 0)*(b 3)*(b 11)+(b 2)*(b 3)*(b 11)+(b 0)*(b 4)*(b 11)+(b 2)*(b 4)*(b 11)+(b 0)*(b 3)*(b 4)*(b 11)+(b 1)*(b 5)*(b 11)+(b 0)*(b 2)*(b 6)*(b 11)+(b 1)*(b 3)*(b 6)*(b 11)+(b 0)*(b 7)*(b 11)+(b 1)*(b 7)*(b 11)+(b 0)*(b 1)*(b 7)*(b 11)+(b 2)*(b 9)*(b 11)+(b 1)*(b 3)*(b 9)*(b 11)+(b 0)*(b 2)*(b 3)*(b 9)*(b 11)+(b 1)*(b 4)*(b 9)*(b 11)+(b 0)*(b 5)*(b 9)*(b 11)+(b 1)*(b 5)*(b 9)*(b 11)+(b 0)*(b 1)*(b 5)*(b 9)*(b 11),
    (b 0)*(b 5)+(b 3)*(b 5)+(b 4)*(b 5)+(b 1)*(b 6)+(b 2)*(b 6)+(b 4)*(b 6)+(b 2)*(b 5)*(b 6)+(b 0)*(b 3)*(b 5)*(b 6)+(b 1)*(b 7)+(b 2)*(b 7)+(b 1)*(b 6)*(b 7)+(b 0)*(b 2)*(b 8)+(b 1)*(b 3)*(b 8)+(b 0)*(b 6)*(b 8)+(b 1)*(b 6)*(b 8)+(b 0)*(b 1)*(b 6)*(b 8)+(b 0)*(b 3)*(b 9)+(b 2)*(b 3)*(b 9)+(b 0)*(b 4)*(b 9)+(b 2)*(b 4)*(b 9)+(b 0)*(b 3)*(b 4)*(b 9)+(b 1)*(b 5)*(b 9)+(b 0)*(b 2)*(b 6)*(b 9)+(b 1)*(b 3)*(b 6)*(b 9)+(b 0)*(b 7)*(b 9)+(b 1)*(b 7)*(b 9)+(b 0)*(b 1)*(b 7)*(b 9)+(b 2)*(b 10)+(b 1)*(b 3)*(b 10)+(b 0)*(b 2)*(b 3)*(b 10)+(b 1)*(b 4)*(b 10)+(b 0)*(b 5)*(b 10)+(b 1)*(b 5)*(b 10)+(b 0)*(b 1)*(b 5)*(b 10),
    (b 3)+(b 4)+(b 3)*(b 4)+(b 2)*(b 5)+(b 2)*(b 3)*(b 5)+(b 0)*(b 4)*(b 5)+(b 0)*(b 6)+(b 1)*(b 6)+(b 0)*(b 1)*(b 6)+(b 0)*(b 2)*(b 6)+(b 0)*(b 3)*(b 6)+(b 1)*(b 3)*(b 6)+(b 2)*(b 3)*(b 6)+(b 0)*(b 4)*(b 6)+(b 2)*(b 4)*(b 6)+(b 0)*(b 3)*(b 4)*(b 6)+(b 1)*(b 5)*(b 6)+(b 0)*(b 7)+(b 1)*(b 7)+(b 0)*(b 1)*(b 7)+(b 0)*(b 2)*(b 7)+(b 1)*(b 3)*(b 7)+(b 0)*(b 6)*(b 7)+(b 1)*(b 6)*(b 7)+(b 0)*(b 1)*(b 6)*(b 7)+(b 2)*(b 8)+(b 1)*(b 3)*(b 8)+(b 0)*(b 2)*(b 3)*(b 8)+(b 1)*(b 4)*(b 8)+(b 0)*(b 5)*(b 8)+(b 1)*(b 5)*(b 8)+(b 0)*(b 1)*(b 5)*(b 8),
    (b 5)+(b 2)*(b 6)+(b 0)*(b 3)*(b 6)+(b 3)*(b 5)*(b 6)+(b 2)*(b 7)+(b 3)*(b 7)+(b 0)*(b 3)*(b 7)+(b 4)*(b 7)+(b 0)*(b 5)*(b 7)+(b 0)*(b 8)+(b 1)*(b 8)+(b 0)*(b 1)*(b 8)+(b 2)*(b 3)*(b 8)+(b 4)*(b 8)+(b 0)*(b 4)*(b 8)+(b 2)*(b 5)*(b 8)+(b 0)*(b 3)*(b 5)*(b 8)+(b 2)*(b 6)*(b 8)+(b 1)*(b 7)*(b 8)+(b 2)*(b 9)+(b 0)*(b 3)*(b 9)+(b 1)*(b 3)*(b 9)+(b 2)*(b 3)*(b 9)+(b 0)*(b 2)*(b 3)*(b 9)+(b 0)*(b 4)*(b 9)+(b 1)*(b 4)*(b 9)+(b 2)*(b 4)*(b 9)+(b 0)*(b 3)*(b 4)*(b 9)+(b 0)*(b 1)*(b 5)*(b 9)+(b 3)*(b 5)*(b 9)+(b 4)*(b 5)*(b 9)+(b 1)*(b 6)*(b 9)+(b 2)*(b 6)*(b 9)+(b 0)*(b 2)*(b 6)*(b 9)+(b 1)*(b 3)*(b 6)*(b 9)+(b 4)*(b 6)*(b 9)+(b 2)*(b 5)*(b 6)*(b 9)+(b 0)*(b 3)*(b 5)*(b 6)*(b 9)+(b 0)*(b 7)*(b 9)+(b 0)*(b 1)*(b 7)*(b 9)+(b 2)*(b 7)*(b 9)+(b 1)*(b 6)*(b 7)*(b 9)+(b 0)*(b 2)*(b 8)*(b 9)+(b 1)*(b 3)*(b 8)*(b 9)+(b 0)*(b 6)*(b 8)*(b 9)+(b 1)*(b 6)*(b 8)*(b 9)+(b 0)*(b 1)*(b 6)*(b 8)*(b 9)+(b 2)*(b 10)+(b 0)*(b 3)*(b 10)+(b 1)*(b 3)*(b 10)+(b 2)*(b 3)*(b 10)+(b 0)*(b 2)*(b 3)*(b 10)+(b 0)*(b 4)*(b 10)+(b 1)*(b 4)*(b 10)+(b 2)*(b 4)*(b 10)+(b 0)*(b 3)*(b 4)*(b 10)+(b 0)*(b 5)*(b 10)+(b 0)*(b 1)*(b 5)*(b 10)+(b 0)*(b 2)*(b 6)*(b 10)+(b 1)*(b 3)*(b 6)*(b 10)+(b 0)*(b 7)*(b 10)+(b 1)*(b 7)*(b 10)+(b 0)*(b 1)*(b 7)*(b 10)+(b 2)*(b 9)*(b 10)+(b 1)*(b 3)*(b 9)*(b 10)+(b 0)*(b 2)*(b 3)*(b 9)*(b 10)+(b 1)*(b 4)*(b 9)*(b 10)+(b 0)*(b 5)*(b 9)*(b 10)+(b 1)*(b 5)*(b 9)*(b 10)+(b 0)*(b 1)*(b 5)*(b 9)*(b 10)+(b 3)*(b 11)+(b 4)*(b 11)+(b 3)*(b 4)*(b 11)+(b 2)*(b 5)*(b 11)+(b 2)*(b 3)*(b 5)*(b 11)+(b 0)*(b 4)*(b 5)*(b 11)+(b 0)*(b 6)*(b 11)+(b 1)*(b 6)*(b 11)+(b 0)*(b 1)*(b 6)*(b 11)+(b 0)*(b 2)*(b 6)*(b 11)+(b 0)*(b 3)*(b 6)*(b 11)+(b 1)*(b 3)*(b 6)*(b 11)+(b 2)*(b 3)*(b 6)*(b 11)+(b 0)*(b 4)*(b 6)*(b 11)+(b 2)*(b 4)*(b 6)*(b 11)+(b 0)*(b 3)*(b 4)*(b 6)*(b 11)+(b 1)*(b 5)*(b 6)*(b 11)+(b 0)*(b 7)*(b 11)+(b 1)*(b 7)*(b 11)+(b 0)*(b 1)*(b 7)*(b 11)+(b 0)*(b 2)*(b 7)*(b 11)+(b 1)*(b 3)*(b 7)*(b 11)+(b 0)*(b 6)*(b 7)*(b 11)+(b 1)*(b 6)*(b 7)*(b 11)+(b 0)*(b 1)*(b 6)*(b 7)*(b 11)+(b 2)*(b 8)*(b 11)+(b 1)*(b 3)*(b 8)*(b 11)+(b 0)*(b 2)*(b 3)*(b 8)*(b 11)+(b 1)*(b 4)*(b 8)*(b 11)+(b 0)*(b 5)*(b 8)*(b 11)+(b 1)*(b 5)*(b 8)*(b 11)+(b 0)*(b 1)*(b 5)*(b 8)*(b 11) ]

private def chart0 (_b : Fin 12 → ZMod 2) : Mat := 1
private theorem column0 (b : Fin 12 → ZMod 2) :
    (chart0 b).mulVec (Pi.single 3 1)=state0 b := by
  rw [chart0,Matrix.one_mulVec]
  funext j
  fin_cases j <;> simp [state0]

private theorem scalar_stage0 (b : Fin 12 → ZMod 2) :
    ∀j : Fin 26,state1 b j=state0 b j+
      b 0*((∑k∈bitRows0 j,state0 b k)-state0 b j) := by
  intro j
  fin_cases j <;> simp [state0,state1,bitRows0] <;>
    ring_nf <;> simp only [two_zero,three_one,mul_zero,zero_mul,mul_one,add_zero,zero_add]

private theorem stage0 (b : Fin 12 → ZMod 2) :
    StageRelation (bitMatrix 0) (b 0) (state0 b) (state1 b) :=
  stage_from_rows (bitMatrix 0) bitRows0 bit_entry0
    (b 0) (state0 b) (state1 b) (scalar_stage0 b)

private def chart1 (b : Fin 12 → ZMod 2) : Mat :=
  affineFactor (b 0) (bitMatrix 0)*chart0 b
private theorem column1 (b : Fin 12 → ZMod 2) :
    (chart1 b).mulVec (Pi.single 3 1)=state1 b :=
  column_from_stage (bitMatrix 0) (chart0 b) (b 0)
    (state0 b) (state1 b) (column0 b) (stage0 b)

private theorem scalar_stage1 (b : Fin 12 → ZMod 2) :
    ∀j : Fin 26,state2 b j=state1 b j+
      b 1*((∑k∈bitRows1 j,state1 b k)-state1 b j) := by
  intro j
  fin_cases j <;> simp [state1,state2,bitRows1] <;>
    ring_nf <;> simp only [two_zero,three_one,mul_zero,zero_mul,mul_one,add_zero,zero_add]

private theorem stage1 (b : Fin 12 → ZMod 2) :
    StageRelation (bitMatrix 1) (b 1) (state1 b) (state2 b) :=
  stage_from_rows (bitMatrix 1) bitRows1 bit_entry1
    (b 1) (state1 b) (state2 b) (scalar_stage1 b)

private def chart2 (b : Fin 12 → ZMod 2) : Mat :=
  affineFactor (b 1) (bitMatrix 1)*chart1 b
private theorem column2 (b : Fin 12 → ZMod 2) :
    (chart2 b).mulVec (Pi.single 3 1)=state2 b :=
  column_from_stage (bitMatrix 1) (chart1 b) (b 1)
    (state1 b) (state2 b) (column1 b) (stage1 b)

private theorem scalar_stage2 (b : Fin 12 → ZMod 2) :
    ∀j : Fin 26,state3 b j=state2 b j+
      b 2*((∑k∈bitRows2 j,state2 b k)-state2 b j) := by
  intro j
  fin_cases j <;> simp [state2,state3,bitRows2] <;>
    ring_nf <;> simp only [two_zero,three_one,mul_zero,zero_mul,mul_one,add_zero,zero_add]

private theorem stage2 (b : Fin 12 → ZMod 2) :
    StageRelation (bitMatrix 2) (b 2) (state2 b) (state3 b) :=
  stage_from_rows (bitMatrix 2) bitRows2 bit_entry2
    (b 2) (state2 b) (state3 b) (scalar_stage2 b)

private def chart3 (b : Fin 12 → ZMod 2) : Mat :=
  affineFactor (b 2) (bitMatrix 2)*chart2 b
private theorem column3 (b : Fin 12 → ZMod 2) :
    (chart3 b).mulVec (Pi.single 3 1)=state3 b :=
  column_from_stage (bitMatrix 2) (chart2 b) (b 2)
    (state2 b) (state3 b) (column2 b) (stage2 b)

private theorem scalar_stage3 (b : Fin 12 → ZMod 2) :
    ∀j : Fin 26,state4 b j=state3 b j+
      b 3*((∑k∈bitRows3 j,state3 b k)-state3 b j) := by
  intro j
  fin_cases j <;> simp [state3,state4,bitRows3] <;>
    ring_nf <;> simp only [two_zero,three_one,mul_zero,zero_mul,mul_one,add_zero,zero_add]

private theorem stage3 (b : Fin 12 → ZMod 2) :
    StageRelation (bitMatrix 3) (b 3) (state3 b) (state4 b) :=
  stage_from_rows (bitMatrix 3) bitRows3 bit_entry3
    (b 3) (state3 b) (state4 b) (scalar_stage3 b)

private def chart4 (b : Fin 12 → ZMod 2) : Mat :=
  affineFactor (b 3) (bitMatrix 3)*chart3 b
private theorem column4 (b : Fin 12 → ZMod 2) :
    (chart4 b).mulVec (Pi.single 3 1)=state4 b :=
  column_from_stage (bitMatrix 3) (chart3 b) (b 3)
    (state3 b) (state4 b) (column3 b) (stage3 b)

private theorem scalar_stage4 (b : Fin 12 → ZMod 2) :
    ∀j : Fin 26,state5 b j=state4 b j+
      b 4*((∑k∈bitRows4 j,state4 b k)-state4 b j) := by
  intro j
  fin_cases j <;> simp [state4,state5,bitRows4] <;>
    ring_nf <;> simp only [two_zero,three_one,mul_zero,zero_mul,mul_one,add_zero,zero_add]

private theorem stage4 (b : Fin 12 → ZMod 2) :
    StageRelation (bitMatrix 4) (b 4) (state4 b) (state5 b) :=
  stage_from_rows (bitMatrix 4) bitRows4 bit_entry4
    (b 4) (state4 b) (state5 b) (scalar_stage4 b)

private def chart5 (b : Fin 12 → ZMod 2) : Mat :=
  affineFactor (b 4) (bitMatrix 4)*chart4 b
private theorem column5 (b : Fin 12 → ZMod 2) :
    (chart5 b).mulVec (Pi.single 3 1)=state5 b :=
  column_from_stage (bitMatrix 4) (chart4 b) (b 4)
    (state4 b) (state5 b) (column4 b) (stage4 b)

private theorem scalar_stage5 (b : Fin 12 → ZMod 2) :
    ∀j : Fin 26,state6 b j=state5 b j+
      b 5*((∑k∈bitRows5 j,state5 b k)-state5 b j) := by
  intro j
  fin_cases j <;> simp [state5,state6,bitRows5] <;>
    ring_nf <;> simp only [two_zero,three_one,mul_zero,zero_mul,mul_one,add_zero,zero_add]

private theorem stage5 (b : Fin 12 → ZMod 2) :
    StageRelation (bitMatrix 5) (b 5) (state5 b) (state6 b) :=
  stage_from_rows (bitMatrix 5) bitRows5 bit_entry5
    (b 5) (state5 b) (state6 b) (scalar_stage5 b)

private def chart6 (b : Fin 12 → ZMod 2) : Mat :=
  affineFactor (b 5) (bitMatrix 5)*chart5 b
private theorem column6 (b : Fin 12 → ZMod 2) :
    (chart6 b).mulVec (Pi.single 3 1)=state6 b :=
  column_from_stage (bitMatrix 5) (chart5 b) (b 5)
    (state5 b) (state6 b) (column5 b) (stage5 b)

private theorem scalar_stage6 (b : Fin 12 → ZMod 2) :
    ∀j : Fin 26,state7 b j=state6 b j+
      b 6*((∑k∈bitRows6 j,state6 b k)-state6 b j) := by
  intro j
  fin_cases j <;> simp [state6,state7,bitRows6] <;>
    ring_nf <;> simp only [two_zero,three_one,mul_zero,zero_mul,mul_one,add_zero,zero_add]

private theorem stage6 (b : Fin 12 → ZMod 2) :
    StageRelation (bitMatrix 6) (b 6) (state6 b) (state7 b) :=
  stage_from_rows (bitMatrix 6) bitRows6 bit_entry6
    (b 6) (state6 b) (state7 b) (scalar_stage6 b)

private def chart7 (b : Fin 12 → ZMod 2) : Mat :=
  affineFactor (b 6) (bitMatrix 6)*chart6 b
private theorem column7 (b : Fin 12 → ZMod 2) :
    (chart7 b).mulVec (Pi.single 3 1)=state7 b :=
  column_from_stage (bitMatrix 6) (chart6 b) (b 6)
    (state6 b) (state7 b) (column6 b) (stage6 b)

private theorem scalar_stage7 (b : Fin 12 → ZMod 2) :
    ∀j : Fin 26,state8 b j=state7 b j+
      b 7*((∑k∈bitRows7 j,state7 b k)-state7 b j) := by
  intro j
  fin_cases j <;> simp [state7,state8,bitRows7] <;>
    ring_nf <;> simp only [two_zero,three_one,mul_zero,zero_mul,mul_one,add_zero,zero_add]

private theorem stage7 (b : Fin 12 → ZMod 2) :
    StageRelation (bitMatrix 7) (b 7) (state7 b) (state8 b) :=
  stage_from_rows (bitMatrix 7) bitRows7 bit_entry7
    (b 7) (state7 b) (state8 b) (scalar_stage7 b)

private def chart8 (b : Fin 12 → ZMod 2) : Mat :=
  affineFactor (b 7) (bitMatrix 7)*chart7 b
private theorem column8 (b : Fin 12 → ZMod 2) :
    (chart8 b).mulVec (Pi.single 3 1)=state8 b :=
  column_from_stage (bitMatrix 7) (chart7 b) (b 7)
    (state7 b) (state8 b) (column7 b) (stage7 b)

private theorem scalar_stage8 (b : Fin 12 → ZMod 2) :
    ∀j : Fin 26,state9 b j=state8 b j+
      b 8*((∑k∈bitRows8 j,state8 b k)-state8 b j) := by
  intro j
  fin_cases j <;> simp [state8,state9,bitRows8] <;>
    ring_nf <;> simp only [two_zero,three_one,mul_zero,zero_mul,mul_one,add_zero,zero_add]

private theorem stage8 (b : Fin 12 → ZMod 2) :
    StageRelation (bitMatrix 8) (b 8) (state8 b) (state9 b) :=
  stage_from_rows (bitMatrix 8) bitRows8 bit_entry8
    (b 8) (state8 b) (state9 b) (scalar_stage8 b)

private def chart9 (b : Fin 12 → ZMod 2) : Mat :=
  affineFactor (b 8) (bitMatrix 8)*chart8 b
private theorem column9 (b : Fin 12 → ZMod 2) :
    (chart9 b).mulVec (Pi.single 3 1)=state9 b :=
  column_from_stage (bitMatrix 8) (chart8 b) (b 8)
    (state8 b) (state9 b) (column8 b) (stage8 b)

private theorem scalar_stage9 (b : Fin 12 → ZMod 2) :
    ∀j : Fin 26,state10 b j=state9 b j+
      b 9*((∑k∈bitRows9 j,state9 b k)-state9 b j) := by
  intro j
  fin_cases j <;> simp [state9,state10,bitRows9] <;>
    ring_nf <;> simp only [two_zero,three_one,mul_zero,zero_mul,mul_one,add_zero,zero_add]

private theorem stage9 (b : Fin 12 → ZMod 2) :
    StageRelation (bitMatrix 9) (b 9) (state9 b) (state10 b) :=
  stage_from_rows (bitMatrix 9) bitRows9 bit_entry9
    (b 9) (state9 b) (state10 b) (scalar_stage9 b)

private def chart10 (b : Fin 12 → ZMod 2) : Mat :=
  affineFactor (b 9) (bitMatrix 9)*chart9 b
private theorem column10 (b : Fin 12 → ZMod 2) :
    (chart10 b).mulVec (Pi.single 3 1)=state10 b :=
  column_from_stage (bitMatrix 9) (chart9 b) (b 9)
    (state9 b) (state10 b) (column9 b) (stage9 b)

private theorem scalar_stage10 (b : Fin 12 → ZMod 2) :
    ∀j : Fin 26,state11 b j=state10 b j+
      b 10*((∑k∈bitRows10 j,state10 b k)-state10 b j) := by
  intro j
  fin_cases j <;> simp [state10,state11,bitRows10] <;>
    ring_nf <;> simp only [two_zero,three_one,mul_zero,zero_mul,mul_one,add_zero,zero_add]

private theorem stage10 (b : Fin 12 → ZMod 2) :
    StageRelation (bitMatrix 10) (b 10) (state10 b) (state11 b) :=
  stage_from_rows (bitMatrix 10) bitRows10 bit_entry10
    (b 10) (state10 b) (state11 b) (scalar_stage10 b)

private def chart11 (b : Fin 12 → ZMod 2) : Mat :=
  affineFactor (b 10) (bitMatrix 10)*chart10 b
private theorem column11 (b : Fin 12 → ZMod 2) :
    (chart11 b).mulVec (Pi.single 3 1)=state11 b :=
  column_from_stage (bitMatrix 10) (chart10 b) (b 10)
    (state10 b) (state11 b) (column10 b) (stage10 b)

private theorem scalar_stage11 (b : Fin 12 → ZMod 2) :
    ∀j : Fin 26,columnThree b j=state11 b j+
      b 11*((∑k∈bitRows11 j,state11 b k)-state11 b j) := by
  intro j
  fin_cases j <;> simp [state11,columnThree,bitRows11] <;>
    ring_nf <;> simp only [two_zero,three_one,mul_zero,zero_mul,mul_one,add_zero,zero_add]

private theorem stage11 (b : Fin 12 → ZMod 2) :
    StageRelation (bitMatrix 11) (b 11) (state11 b) (columnThree b) :=
  stage_from_rows (bitMatrix 11) bitRows11 bit_entry11
    (b 11) (state11 b) (columnThree b) (scalar_stage11 b)

private def chart12 (b : Fin 12 → ZMod 2) : Mat :=
  affineFactor (b 11) (bitMatrix 11)*chart11 b
private theorem column12 (b : Fin 12 → ZMod 2) :
    (chart12 b).mulVec (Pi.single 3 1)=columnThree b :=
  column_from_stage (bitMatrix 11) (chart11 b) (b 11)
    (state11 b) (columnThree b) (column11 b) (stage11 b)

private theorem chart_equal (b : Fin 12 → ZMod 2) :
    chart12 b=CFSGReeFFourBinaryFirstGlobalEntry.chartMatrix b := rfl

theorem chart_column_three (b : Fin 12 → ZMod 2) :
    (CFSGReeFFourBinaryFirstGlobalEntry.chartMatrix b).mulVec (Pi.single 3 1)=
      columnThree b := by
  rw [←chart_equal b]
  exact column12 b

theorem outer_column_two : ∀k : Fin 26,
    outerMatrix k 2=(if k=2 then 1 else 0)+(if k=3 then 1 else 0) := by
  decide +kernel

theorem outer_row_one : ∀k : Fin 26,
    outerMatrix 1 k=if k=1 then 1 else 0 := by
  decide +kernel

theorem commutator_entry_one_two_eq (M : Mat) :
    (M*outerMatrix-outerMatrix*M) 1 2=M 1 3 := by
  change (∑k : Fin 26,M 1 k*outerMatrix k 2)-
    (∑k : Fin 26,outerMatrix 1 k*M k 2)=M 1 3
  simp_rw [outer_column_two,outer_row_one]
  simp [add_mul,mul_add,mul_ite,ite_mul,Finset.sum_add_distrib] <;> ring

theorem third_constraint_entry (b : Fin 12 → ZMod 2) :
    CFSGReeFFourBinaryFirstGlobalEntry.chartMatrix b 1 3=
      b 3+b 4+b 2*b 6+b 0*b 3*b 6+b 0*b 9+b 1*b 9+
      b 0*b 1*b 9+b 2*b 9+b 1*b 6*b 9+b 0*b 10+b 1*b 10+b 0*b 1*b 10 := by
  rw [←chart_equal b]
  have h := congrFun (column12 b) (1 : Fin 26)
  rw [Matrix.mulVec_single_one] at h
  simpa [columnThree,Matrix.col_apply] using h

theorem third_constraint_commutator_entry (b : Fin 12 → ZMod 2) :
    (CFSGReeFFourBinaryFirstGlobalEntry.chartMatrix b*outerMatrix-
      outerMatrix*CFSGReeFFourBinaryFirstGlobalEntry.chartMatrix b) 1 2=
      b 3+b 4+b 2*b 6+b 0*b 3*b 6+b 0*b 9+b 1*b 9+
      b 0*b 1*b 9+b 2*b 9+b 1*b 6*b 9+b 0*b 10+b 1*b 10+b 0*b 1*b 10 := by
  rw [commutator_entry_one_two_eq,third_constraint_entry]

end SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryThirdGlobalColumn
