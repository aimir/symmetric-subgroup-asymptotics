import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Fintype.EquivFin

/-! A computable pair-coordinate model of F4. Its defining relation is
omega²=1+omega; the base-field nonroot check has only two scalar cases. -/

set_option autoImplicit false

namespace SymmetricSubgroupAsymptotics
namespace BinaryQuadraticField

abbrev Scalar := QuadraticAlgebra (ZMod 2) 1 1

instance no_root : Fact (∀ r : ZMod 2, r ^ 2 ≠ 1 + 1 * r) := ⟨by decide +kernel⟩

instance : Fintype Scalar := Fintype.ofEquiv (ZMod 2 × ZMod 2)
  (QuadraticAlgebra.equivProd 1 1).symm

def omega : Scalar := ⟨0, 1⟩

theorem scalar_eq (z : Scalar) :
    z = z.re • (1 : Scalar) + z.im • omega := by
  simpa only [omega, ← Algebra.algebraMap_eq_smul_one] using
    QuadraticAlgebra.mk_eq_add_smul_omega z.re z.im

end BinaryQuadraticField
end SymmetricSubgroupAsymptotics
