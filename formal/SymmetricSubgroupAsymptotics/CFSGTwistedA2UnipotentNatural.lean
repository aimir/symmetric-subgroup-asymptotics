import SymmetricSubgroupAsymptotics.CFSGTwistedA2UnipotentArrays
import SymmetricSubgroupAsymptotics.CFSGTwistedA2HighestRootUnits

/-! Every literal upper unitary-unipotent array is an ACTUAL natural
A2 elementary word. The off-diagonal parameter is retained, rather than
asserting a named-group identification. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGTwistedA2UnipotentArrays
open CFSGTwistedANaturalMatrices CFSGTwistedA2HighestRootUnits CFSGSerreSquareZeroMatrix
variable (K : Type) [Field K] (σ : K ≃+* K)

def upperNatural (a b : K) : NaturalElementary K 2 :=
  elementaryRoot K (naturalRootUnit K 2) false 0 a *
    elementaryRoot K (naturalRootUnit K 2) false 1 (σ a) *
      highest K (b - a * σ a)

theorem upperNatural_val (a b : K) :
    ((upperNatural K σ a b).val : Mat K 2) = upperArray σ a b := by
  change ((naturalRootUnit K 2 false 0 a : Mat K 2) *
    (naturalRootUnit K 2 false 1 (σ a) : Mat K 2)) *
      ((highest K (b - a * σ a)).val : Mat K 2) = _
  rw [naturalRootUnit_positive_zero, naturalRootUnit_positive_one, highest_val]
  simp only [entryUnit_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upperArray, Matrix.mul_apply, Fin.sum_univ_three, Matrix.single,
      Matrix.one_apply] <;> (try simp only [Fin.ext_iff]) <;> (try norm_num) <;> ring

theorem upperNatural_unit (a b : K) :
    (upperNatural K σ a b).val = upperUnit σ a b := by
  apply Units.ext
  exact upperNatural_val K σ a b

end SymmetricSubgroupAsymptotics.CFSGTwistedA2UnipotentArrays
