import SymmetricSubgroupAsymptotics.PermutationCycleCoordinateChart
import Mathlib.Logic.Equiv.Basic

/-! The actual disjoint cyclic coordinates of a finite permutation.
The index set is its SameCycle quotient, not a supplied cycle menu. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PermutationCycleDecomposition
open PermutationCycleCoordinateChart
variable {I : Type*} [Finite I] (σ : Equiv.Perm I)

abbrev CycleIndex := Quotient (Equiv.Perm.SameCycle.setoid σ)

def cycleClass (i : I) : CycleIndex σ := Quotient.mk _ i

def cycleLength (c : CycleIndex σ) : ℕ :=
  Function.minimalPeriod (σ : I → I) c.out

theorem cycleLength_pos (c : CycleIndex σ) : 0<cycleLength σ c :=
  PermutationCycleCoordinateChart.cycleLength_pos σ c.out

def orbitFiberEquiv (c : CycleIndex σ) :
    {y : I // σ.SameCycle c.out y} ≃ {y : I // cycleClass σ y=c} :=
  Equiv.subtypeEquivRight (fun y => by
    have hout : cycleClass σ c.out=c := Quotient.out_eq' c
    constructor
    · intro h
      have he : cycleClass σ c.out=cycleClass σ y := Quotient.sound h
      exact he.symm.trans hout
    · intro h
      exact Quotient.exact (hout.trans h.symm))

def pointChart : (Σc : CycleIndex σ,Fin (cycleLength σ c)) ≃ I :=
  (Equiv.sigmaCongrRight (fun c : CycleIndex σ =>
    (show Fin (cycleLength σ c) ≃ {y : I // cycleClass σ y=c} from
      (orbitChart σ c.out).trans (orbitFiberEquiv σ c)))).trans
      (Equiv.sigmaFiberEquiv (cycleClass σ))

theorem pointChart_apply (c : CycleIndex σ) (i : Fin (cycleLength σ c)) :
    pointChart σ ⟨c,i⟩=(orbitChart σ c.out i).val := rfl

theorem cycleClass_pointChart (c : CycleIndex σ) (i : Fin (cycleLength σ c)) :
    cycleClass σ (pointChart σ ⟨c,i⟩)=c :=
  ((orbitFiberEquiv σ c) (orbitChart σ c.out i)).property

theorem pointChart_rotate (c : CycleIndex σ) (i : Fin (cycleLength σ c)) :
    pointChart σ ⟨c,finRotate _ i⟩=σ (pointChart σ ⟨c,i⟩) :=
  orbitChart_rotate σ c.out i

end SymmetricSubgroupAsymptotics.PermutationCycleDecomposition
