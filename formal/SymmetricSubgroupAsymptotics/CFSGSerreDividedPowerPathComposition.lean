import SymmetricSubgroupAsymptotics.CFSGSerreDividedPowerPaths
import SymmetricSubgroupAsymptotics.CFSGSerreDividedPowers

/-! Parent-path identities in the SAME original integral lattice.
Appending one step applies its actual integral divided-power operator;
two successive unit steps give twice the double-step vector. These
identities supply whole-family parent certificates without expanding
the earlier source path or assuming any matrix faithfulness. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSerreDividedPowerPathComposition
open CFSG.Models.Chevalley CFSGSerreDividedPowerPaths CFSGSerreDividedPowers
variable {r:ℕ} (A:Matrix (Fin r) (Fin r) ℤ)

theorem applySteps_append (neg:Bool) (ss ts:List (Fin r×ℕ)) (x:integralLattice A) :
    applySteps A neg (ss++ts) x=applySteps A neg ts (applySteps A neg ss x) := by
  induction ss generalizing x with
  | nil=>rfl
  | cons s ss ih=>exact ih (integralOperator A neg s.1 s.2 x)

theorem path_append_step (neg:Bool) (start:Fin r) (ss:List (Fin r×ℕ)) (i:Fin r) (k:ℕ) :
    pathVector A neg start (ss++[(i,k)])=
      integralOperator A neg i k (pathVector A neg start ss) := by
  unfold pathVector
  rw [applySteps_append]
  rfl

theorem path_append_one_val (neg:Bool) (start:Fin r) (ss:List (Fin r×ℕ)) (i:Fin r) :
    (pathVector A neg start (ss++[(i,1)])).val=
      ⁅rootVector A neg i,(pathVector A neg start ss).val⁆ := by
  rw [path_append_step]
  change dividedPower A neg i 1 (pathVector A neg start ss).val=_
  simp [dividedPower]

theorem path_double_step (neg:Bool) (start:Fin r) (ss:List (Fin r×ℕ)) (i:Fin r) :
    integralOperator A neg i 1 (pathVector A neg start (ss++[(i,1)]))=
      (2:ℕ) • pathVector A neg start (ss++[(i,2)]) := by
  rw [path_append_step,path_append_step]
  have h:=congrArg (fun D:Module.End ℤ (integralLattice A)=>D (pathVector A neg start ss))
    (integralOperator_mul A neg i 1 1)
  change integralOperator A neg i 1 (integralOperator A neg i 1 (pathVector A neg start ss))=
    (2:ℕ) • integralOperator A neg i 2 (pathVector A neg start ss) at h
  exact h

end SymmetricSubgroupAsymptotics.CFSGSerreDividedPowerPathComposition
