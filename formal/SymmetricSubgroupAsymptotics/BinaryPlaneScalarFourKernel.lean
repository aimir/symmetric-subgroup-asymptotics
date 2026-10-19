import SymmetricSubgroupAsymptotics.BinaryPlanePermutationAffineEquiv
import SymmetricSubgroupAsymptotics.ScalarFourHeadDefinitions

/-! Scalar-four coordinates on the actual translation kernel of S4.
The selected cubic is a displayed two-by-two binary matrix. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPlaneScalarFourKernel
open BinaryPlanePermutationAffineEquiv LinearSemidirectCoprimeSocleBounds

def cubic : Linear where
  toFun v := ![v 1,v 0+v 1]
  invFun v := ![v 0+v 1,v 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_add' := by decide +kernel
  map_smul' := by decide +kernel

def planePair : Multiplicative Plane →* ScalarFour where
  toFun v := Multiplicative.ofAdd (v.toAdd 0,v.toAdd 1)
  map_one' := rfl
  map_mul' _ _ := rfl

theorem planePair_injective : Function.Injective planePair := by
  intro v w h
  apply Multiplicative.toAdd.injective
  funext i
  fin_cases i
  · exact congrArg (fun z : ScalarFour => z.toAdd.1) h
  · exact congrArg (fun z : ScalarFour => z.toAdd.2) h

private def kernelAffine : linearPart.ker →*
    translationKernel (MonoidHom.id Linear) where
  toFun p := ⟨affineMap p,p.property⟩
  map_one' := Subtype.ext affineMap.map_one
  map_mul' p q := Subtype.ext (affineMap.map_mul p q)

def coord : linearPart.ker →* ScalarFour :=
  planePair.comp ((translationEquiv (MonoidHom.id Linear)).toMonoidHom.comp kernelAffine)

@[simp] theorem coord_apply (p : linearPart.ker) :
    coord p=Multiplicative.ofAdd ((p : Equiv.Perm Plane) 0 0,(p : Equiv.Perm Plane) 0 1) := rfl

theorem coord_injective : Function.Injective coord := by
  apply planePair_injective.comp
  apply (translationEquiv (MonoidHom.id Linear)).injective.comp
  intro p q h
  apply Subtype.ext
  exact affineMap_injective (congrArg Subtype.val h)

private theorem pair_cubic (v : Plane) :
    planePair (Multiplicative.ofAdd (cubic v))=
      scalarFourTwist 1 (planePair (Multiplicative.ofAdd v)) := by
  revert v
  decide +kernel

/-- The conjugation identity uses the actual permutation's affine image. -/
theorem coord_conjugate (g : Equiv.Perm Plane) (hg : linearPart g=cubic)
    (p : linearPart.ker) :
    coord (MulAut.conjNormal g p)=scalarFourTwist 1 (coord p) := by
  have hp : affineMap (p : Equiv.Perm Plane)=
      SemidirectProduct.inl (Multiplicative.ofAdd ((p : Equiv.Perm Plane) 0)) := by
    apply SemidirectProduct.ext
    · rfl
    · exact p.property
  have hc := conjugate_translation (MonoidHom.id Linear) (affineMap g)
    (Multiplicative.ofAdd ((p : Equiv.Perm Plane) 0))
  rw [← hp,← map_inv,← map_mul,← map_mul] at hc
  have hv := congrArg (fun z : BinaryPlanePermutationAffineEquiv.Model => z.left.toAdd) hc
  change (g*(p : Equiv.Perm Plane)*g⁻¹) 0=linearPart g ((p : Equiv.Perm Plane) 0) at hv
  change planePair (Multiplicative.ofAdd ((g*(p : Equiv.Perm Plane)*g⁻¹) 0))=_
  rw [hv,hg]
  exact pair_cubic _
end SymmetricSubgroupAsymptotics.BinaryPlaneScalarFourKernel
