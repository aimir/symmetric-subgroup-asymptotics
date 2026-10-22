import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Field.Rat
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! The literal coordinate-height sign used by the Geck invariant Gram
matrix. It changes sign on every coordinate simple-root step. -/
set_option autoImplicit false
set_option Elab.async false
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGIntegerHeightSign
variable {n : Type*} [Fintype n] [DecidableEq n]

def height (x : n→ℤ) : ℤ := ∑ i,x i
def heightSign (x : n→ℤ) : ℚ := (-1:ℚ)^height x

theorem height_add (x y : n→ℤ) : height (x+y)=height x+height y := by
  simp only [height,Pi.add_apply,Finset.sum_add_distrib]

theorem height_neg (x : n→ℤ) : height (-x)= -height x := by
  simp only [height,Pi.neg_apply,Finset.sum_neg_distrib]

theorem heightSign_add (x y : n→ℤ) : heightSign (x+y)=heightSign x*heightSign y := by
  rw [heightSign,height_add,zpow_add₀ (by norm_num : (-1:ℚ)≠0)]
  rfl

theorem heightSign_neg (x : n→ℤ) : heightSign (-x)=heightSign x := by
  simp only [heightSign,height_neg,zpow_neg,←inv_zpow]
  norm_num

theorem heightSign_single (i : n) : heightSign (Pi.single i 1)= -1 := by
  have hh : height (Pi.single i 1)=1 := by
    simp only [height,Pi.single_apply,Finset.sum_ite_eq',Finset.sum_ite_eq,
      Finset.mem_univ,if_true]
  rw [heightSign,hh]
  norm_num

theorem heightSign_step (x : n→ℤ) (i : n) :
    heightSign (x+Pi.single i 1)= -heightSign x := by
  rw [heightSign_add,heightSign_single]
  ring

theorem heightSign_ne_zero (x : n→ℤ) : heightSign x≠0 := zpow_ne_zero _ (by norm_num)

end SymmetricSubgroupAsymptotics.CFSGIntegerHeightSign
