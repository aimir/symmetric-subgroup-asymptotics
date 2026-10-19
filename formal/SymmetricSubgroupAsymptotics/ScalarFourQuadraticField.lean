import SymmetricSubgroupAsymptotics.ScalarFourHeadDefinitions
import SymmetricSubgroupAsymptotics.BinaryQuadraticField

/-! Literal scalar-four group coordinates agree with the existing field
model. The selected cubic twist is multiplication by the same omega. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ScalarFourQuadraticField
open BinaryQuadraticField

def equivalence : ScalarFour ≃* Multiplicative Scalar where
  toFun x := Multiplicative.ofAdd ⟨x.toAdd.1,x.toAdd.2⟩
  invFun x := Multiplicative.ofAdd (x.toAdd.re,x.toAdd.im)
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem twist_omega (x : ScalarFour) :
    (equivalence (scalarFourTwist 1 x)).toAdd=omega*(equivalence x).toAdd := by
  revert x
  decide +kernel

/-- The same literal tuple, with no coordinate choices or enlarged space. -/
def tupleEquivalence (d : ℕ) : (Fin d → ScalarFour) ≃*
    Multiplicative (Fin d → Scalar) where
  toFun x := Multiplicative.ofAdd (fun i => (equivalence (x i)).toAdd)
  invFun x i := equivalence.symm (Multiplicative.ofAdd (x.toAdd i))
  left_inv x := by funext i; exact equivalence.symm_apply_apply (x i)
  right_inv x := by
    apply Multiplicative.toAdd.injective
    funext i
    exact congrArg Multiplicative.toAdd
      (equivalence.apply_symm_apply (Multiplicative.ofAdd (x.toAdd i)))
  map_mul' _ _ := rfl

theorem tuple_twist (d : ℕ) (x : Fin d → ScalarFour) :
    (tupleEquivalence d (fun i => scalarFourTwist 1 (x i))).toAdd=
      fun i => omega*(tupleEquivalence d x).toAdd i := by
  funext i
  exact twist_omega (x i)

end SymmetricSubgroupAsymptotics.ScalarFourQuadraticField
