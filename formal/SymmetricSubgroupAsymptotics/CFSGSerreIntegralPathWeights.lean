import SymmetricSubgroupAsymptotics.CFSGSerreIntegralLieAlgebra
import SymmetricSubgroupAsymptotics.CFSGSerreDividedPowerPaths

/-! Integer Cartan weights for literal original divided-power paths.
These are equalities inside the SAME integral Lie lattice, hence survive
base change in every characteristic. No source representation is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSerreIntegralPathWeights
open CFSG.Models.Chevalley CFSGSerreDiagram CFSGSerreSignedRootWeights
open CFSGSerreDividedPowerPaths CFSGSerreIntegralLieAlgebra
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ)

def weightSteps (i : Fin r) : List (Fin r×ℕ)→ℤ→ℤ
  | [],mu=>mu
  | s::ss,mu=>weightSteps i ss ((s.2:ℤ)*A i s.1+mu)

def pathWeight (i start : Fin r) (ss : List (Fin r×ℕ)) : ℤ :=
  weightSteps A i ss (A i start)

theorem cast_weightSteps (i : Fin r) (ss : List (Fin r×ℕ)) (mu : ℤ) :
    (weightSteps A i ss mu:ℚ)=CFSGSerreDividedPowerPaths.weightSteps A i ss (mu:ℚ) := by
  induction ss generalizing mu with
  | nil => rfl
  | cons s ss ih =>
    simp only [weightSteps,CFSGSerreDividedPowerPaths.weightSteps,ih,
      Int.cast_add,Int.cast_mul,Int.cast_natCast]

theorem cast_pathWeight (i start : Fin r) (ss : List (Fin r×ℕ)) :
    (pathWeight A i start ss:ℚ)=CFSGSerreDividedPowerPaths.pathWeight A i start ss :=
  cast_weightSteps A i ss (A i start)

def integralCoroot (neg : Bool) (i : Fin r) : integralLattice A :=
  if neg then -latticeGenerator A (.H i) else latticeGenerator A (.H i)

theorem integralCoroot_val (neg : Bool) (i : Fin r) :
    (integralCoroot A neg i).val=coroot A neg i := by cases neg <;> rfl

theorem coroot_path (neg : Bool) (i start : Fin r) (ss : List (Fin r×ℕ)) :
    ⁅integralCoroot A neg i,pathVector A neg start ss⁆=
      pathWeight A i start ss • pathVector A neg start ss := by
  apply Subtype.ext
  rw [integralBracket_val,integralCoroot_val,Submodule.coe_smul]
  rw [←Int.cast_smul_eq_zsmul ℚ,cast_pathWeight]
  exact CFSGSerreDividedPowerPaths.pathVector_weight A neg i start ss

theorem H_path (neg : Bool) (i start : Fin r) (ss : List (Fin r×ℕ)) :
    ⁅latticeGenerator A (.H i),pathVector A neg start ss⁆=
      (if neg then -pathWeight A i start ss else pathWeight A i start ss) •
        pathVector A neg start ss := by
  have h:=coroot_path A neg i start ss
  cases neg
  · simpa [integralCoroot] using h
  · simpa [integralCoroot,neg_lie,neg_smul] using congrArg Neg.neg h

theorem H_scaled_path (neg : Bool) (i start : Fin r) (ss : List (Fin r×ℕ)) (z : ℤ) :
    ⁅latticeGenerator A (.H i),z • pathVector A neg start ss⁆=
      (if neg then -pathWeight A i start ss else pathWeight A i start ss) •
        (z • pathVector A neg start ss) := by
  rw [lie_smul,H_path,smul_smul,smul_smul]
  rw [mul_comm z]

end SymmetricSubgroupAsymptotics.CFSGSerreIntegralPathWeights
