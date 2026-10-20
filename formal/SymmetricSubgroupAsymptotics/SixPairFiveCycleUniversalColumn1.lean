import SymmetricSubgroupAsymptotics.BinarySixPointFiveCyclePolynomial
import SymmetricSubgroupAsymptotics.SixPointFiveCyclePrimitive
import Mathlib.Data.Fintype.Perm

/-! Small selected finite polynomial check: basis column 1, six output
coordinates, and the720 actual permutations of six points. No subgroups,
normal census, generated-group exporter, or owner classification occurs. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SixPairFiveCycleUniversalPolynomial
open BinarySixPointFiveCyclePolynomial

theorem column1 (q : Equiv.Perm (Fin 6)) (hq : q 5≠5) (x : Fin 6) :
    actualOperator representation SixPointFiveCyclePrimitive.cycle q (Pi.single 1 1) x=
      operator 0 (Pi.single 1 1) x := by
  revert q x
  decide +kernel

end SymmetricSubgroupAsymptotics.SixPairFiveCycleUniversalPolynomial
