import SymmetricSubgroupAsymptotics.CFSGSerreIntegralLieAlgebra

/-! The divided Leibniz identity on the same integral lattice and after
arbitrary field base change. No factorial is inverted in the field. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators TensorProduct
namespace SymmetricSubgroupAsymptotics.CFSGSerreIntegralDividedPowerLie
open CFSG.Models.Chevalley CFSGSerreIntegralLieAlgebra
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ)

theorem integralOperator_lie (negative : Bool) (i : Fin r) (k : ℕ)
    (x y : integralLattice A) :
    integralOperator A negative i k ⁅x,y⁆ =
      ∑ j ∈ Finset.range (k+1),
        ⁅integralOperator A negative i j x, integralOperator A negative i (k-j) y⁆ := by
  apply integralInclusion_injective A
  rw [map_sum]
  change dividedPower A negative i k ⁅x.val,y.val⁆ =
    ∑ j ∈ Finset.range (k+1),
      ⁅dividedPower A negative i j x.val, dividedPower A negative i (k-j) y.val⁆
  exact CFSGSerreDividedPowerLieLeibniz.dividedPower_lie A negative i k x.val y.val

variable (K : Type) [Field K]

private theorem space_add_lie (x y z : Space A K) :
    ⁅x+y,z⁆ = ⁅x,z⁆+⁅y,z⁆ := LieRing.add_lie x y z

private theorem space_lie_add (x y z : Space A K) :
    ⁅x,y+z⁆ = ⁅x,y⁆+⁅x,z⁆ := LieRing.lie_add x y z

private theorem space_zero_lie (y : Space A K) : ⁅(0 : Space A K),y⁆ = 0 :=
  (AddMonoidHom.mk' (fun x : Space A K => ⁅x,y⁆)
    (fun x z => space_add_lie A K x z y)).map_zero

private theorem space_lie_zero (x : Space A K) : ⁅x,(0 : Space A K)⁆ = 0 :=
  (AddMonoidHom.mk' (fun y : Space A K => ⁅x,y⁆)
    (space_lie_add A K x)).map_zero

theorem baseChangeIntegralOperator_lie (negative : Bool) (i : Fin r) (k : ℕ)
    (x y : Space A K) :
    (integralOperator A negative i k).baseChange K ⁅x,y⁆ =
      ∑ j ∈ Finset.range (k+1),
        ⁅(integralOperator A negative i j).baseChange K x,
          (integralOperator A negative i (k-j)).baseChange K y⁆ := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [space_zero_lie, map_zero, Finset.sum_const_zero]
  | tmul a u =>
    induction y using TensorProduct.induction_on with
    | zero => simp only [space_lie_zero, map_zero, Finset.sum_const_zero]
    | tmul b v =>
      simp only [spaceBracket_tmul, LinearMap.baseChange_tmul]
      rw [integralOperator_lie]
      simp only [TensorProduct.tmul_sum]
    | add y z hy hz =>
      simp only [space_lie_add, map_add, hy, hz, Finset.sum_add_distrib]
  | add x z hx hz =>
    simp only [space_add_lie, map_add, hx, hz, Finset.sum_add_distrib]

end SymmetricSubgroupAsymptotics.CFSGSerreIntegralDividedPowerLie
