import SymmetricSubgroupAsymptotics.CFSGSerreSignedRootWeights
import SymmetricSubgroupAsymptotics.CFSGSerreDiagramLattice

/-! Genuine original integral vectors obtained by specified finite
simple divided-power paths. Their rational Cartan weights are tracked
in parallel with the same path. No spanning or independence assertion
is built into this family constructor. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSerreDividedPowerPaths
open CFSG.Models.Chevalley CFSGSerreDiagram CFSGSerreSignedRootWeights
variable {r:ℕ} (A:Matrix (Fin r) (Fin r) ℤ)

def applySteps (neg:Bool) : List (Fin r×ℕ)→integralLattice A→integralLattice A
  | [],x=>x
  | s::ss,x=>applySteps neg ss (integralOperator A neg s.1 s.2 x)

def weightSteps (i:Fin r) : List (Fin r×ℕ)→ℚ→ℚ
  | [],mu=>mu
  | s::ss,mu=>weightSteps i ss ((s.2:ℚ)*(A i s.1:ℚ)+mu)

def pathVector (neg:Bool) (start:Fin r) (steps:List (Fin r×ℕ)) : integralLattice A :=
  applySteps A neg steps (latticeGenerator A (if neg then .F start else .E start))

def pathWeight (i start:Fin r) (steps:List (Fin r×ℕ)) : ℚ :=
  weightSteps A i steps (A i start:ℚ)

theorem applySteps_weight (neg:Bool) (i:Fin r) (steps:List (Fin r×ℕ))
    (x:integralLattice A) (mu:ℚ) (hx:⁅coroot A neg i,x.val⁆=mu • x.val) :
    ⁅coroot A neg i,(applySteps A neg steps x).val⁆=
      weightSteps A i steps mu • (applySteps A neg steps x).val := by
  induction steps generalizing x mu with
  | nil=>exact hx
  | cons s ss ih=>
    exact ih (integralOperator A neg s.1 s.2 x) ((s.2:ℚ)*(A i s.1:ℚ)+mu)
      (coroot_dividedPower A neg i s.1 x.val mu hx s.2)

theorem pathVector_weight (neg:Bool) (i start:Fin r) (steps:List (Fin r×ℕ)) :
    ⁅coroot A neg i,(pathVector A neg start steps).val⁆=
      pathWeight A i start steps • (pathVector A neg start steps).val :=
  applySteps_weight A neg i steps _ (A i start:ℚ) (coroot_root A neg i start)

end SymmetricSubgroupAsymptotics.CFSGSerreDividedPowerPaths
