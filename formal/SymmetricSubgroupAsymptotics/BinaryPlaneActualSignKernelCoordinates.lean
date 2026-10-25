import SymmetricSubgroupAsymptotics.BinaryPlaneKernelClassSignDescent
import SymmetricSubgroupAsymptotics.LinearSemidirectSubgroupKernelChart

/-! Literal coordinates on the top kernel of the ACTUAL sign image.
The original binary signs and original block top are retained. Conjugation
is the actual permutation of coordinates even for sign-carrying lifts. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryPlaneActualSignKernelCoordinates
open BinaryPlanePermutationAffineEquiv BinaryPlaneWreathIrreducible
open BinaryPlaneWreathActualOddKernel BinaryPlaneWreathNormalGenerators
open SemidirectProduct

variable {R I : Type} [Group R] [Finite R] [MulAction R I]
    [Fintype I] [DecidableEq I] (C : Subgroup (W (R := R) (I := I)))

abbrev Image := (signProjection C).range

def top : Image C →* R :=
  (rightHom : Sign (R := R) (I := I) →* R).comp (Image C).subtype

abbrev Kernel := (top C).ker

private theorem kernel_right (u : Kernel C) :
    (((u : Image C) : Sign (R := R) (I := I))).right = 1 := u.property

def coordinate (i : I) : Kernel C →* Multiplicative (ZMod 2) where
  toFun u := Multiplicative.ofAdd ((((u : Image C) : Sign (R := R) (I := I)).left).toAdd.val i)
  map_one' := rfl
  map_mul' u v := by
    apply Multiplicative.toAdd.injective
    change (((((u : Image C) : Sign (R := R) (I := I)).left *
      LinearSemidirectCoprimeSocleBounds.linearAction
        (CyclicOrbitBinarySignNormalGenerators.linearAction
          (TernaryPermutationWreathEmbedding.signs (R := R) (I := I)))
        (((u : Image C) : Sign (R := R) (I := I)).right)
        (((v : Image C) : Sign (R := R) (I := I)).left)).toAdd).val i) = _
    rw [kernel_right,map_one]
    rfl

theorem coordinate_joint_injective :
    Function.Injective (fun u : Kernel C => fun i : I => coordinate C i u) := by
  intro u v he
  apply Subtype.ext
  apply Subtype.ext
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    apply Subtype.ext
    funext i
    exact congrArg Multiplicative.toAdd (congrFun he i)
  · exact (kernel_right C u).trans (kernel_right C v).symm

theorem coordinate_conjugation (q : Image C) (u : Kernel C) (i : I) :
    coordinate C i ((MulAut.conjNormal q) u) =
      coordinate C (((q : Sign (R := R) (I := I)).right)⁻¹ • i) u := by
  let rho := CyclicOrbitBinarySignNormalGenerators.linearAction
    (TernaryPermutationWreathEmbedding.signs (R := R) (I := I))
  let qS : Sign (R := R) (I := I) := q
  let uS : Sign (R := R) (I := I) := (u : Image C)
  have hu : (inl uS.left : Sign (R := R) (I := I)) = uS := by
    apply SemidirectProduct.ext
    · rfl
    · exact (kernel_right C u).symm
  have hc : qS*uS*qS⁻¹ = inl (LinearSemidirectCoprimeSocleBounds.linearAction rho qS.right uS.left) := by
    calc
      qS*uS*qS⁻¹ = qS*inl uS.left*qS⁻¹ := by rw [hu]
      _ = _ := LinearSemidirectCoprimeSocleBounds.conjugate_translation rho qS uS.left
  apply Multiplicative.toAdd.injective
  have hh := congrArg (fun z : Sign (R := R) (I := I) => z.left.toAdd.val i) hc
  exact hh

theorem coordinate_of_actual_lift (u : Kernel C) (h : C)
    (he : ((u : Image C) : Sign (R := R) (I := I)) = signProjection C h) (i : I) :
    coordinate C i u = oddMarkerSign (toThree ((h : W (R := R) (I := I)).left i)) := by
  apply Multiplicative.toAdd.injective
  change (((u : Image C) : Sign (R := R) (I := I)).left).toAdd.val i = _
  rw [he]
  rfl

end SymmetricSubgroupAsymptotics.BinaryPlaneActualSignKernelCoordinates
