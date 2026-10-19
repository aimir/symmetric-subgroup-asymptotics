import SymmetricSubgroupAsymptotics.StandardGLThreeCentralDeterminantSplit
import Mathlib.Tactic.NormNum

/-! Explicit elementary matrices certify that the standard simple groups
used in the small affine rows are nonabelian. -/
set_option autoImplicit false
noncomputable section
open scoped IsMulCommutative
namespace SymmetricSubgroupAsymptotics.StandardThreeDimensionalLinearGroups

variable (p : ℕ) [Fact p.Prime]

def elementary12 : SpecialThree p :=
  ⟨![![1, 1, 0], ![0, 1, 0], ![0, 0, 1]], by
    norm_num [Matrix.det_fin_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two]⟩

def elementary23 : SpecialThree p :=
  ⟨![![1, 0, 0], ![0, 1, 1], ![0, 0, 1]], by
    norm_num [Matrix.det_fin_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two]⟩

theorem noncommutative_SL : ¬ IsMulCommutative (SpecialThree p) := by
  intro h
  letI : IsMulCommutative (SpecialThree p) := h
  have he := congrArg (fun g : SpecialThree p => g.val 0 2)
    (mul_comm (elementary12 p) (elementary23 p))
  have h10 : (1 : ZMod p) = 0 := by
    simpa [elementary12, elementary23, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_apply, Fin.sum_univ_succ] using he
  exact one_ne_zero h10

local instance standardNoncommPrimeTwo : Fact (Nat.Prime 2) := ⟨by decide⟩
local instance standardNoncommPrimeThree : Fact (Nat.Prime 3) := ⟨by decide⟩

theorem noncommutative_GL_two : ¬ IsMulCommutative (GeneralThree 2) := by
  intro h
  letI : IsMulCommutative (GeneralThree 2) := h
  apply noncommutative_SL 2
  refine ⟨⟨?_⟩⟩
  intro x y
  apply specialLinearGeneralTwoEquiv.injective
  rw [map_mul, map_mul, mul_comm]

theorem noncommutative_determinantKernelThree :
    ¬ IsMulCommutative determinantKernelThree := by
  intro h
  letI : IsMulCommutative determinantKernelThree := h
  apply noncommutative_SL 3
  refine ⟨⟨?_⟩⟩
  intro x y
  apply (specialLinearKerEquiv 3).injective
  rw [map_mul, map_mul, mul_comm]

end SymmetricSubgroupAsymptotics.StandardThreeDimensionalLinearGroups
