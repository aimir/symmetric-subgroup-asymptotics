import SymmetricSubgroupAsymptotics.CFSGSymplecticRankTwoSiegelEmbedding
import Mathlib.GroupTheory.SemidirectProduct

/-! The literal congruence action and actual shear/double conjugation
supply a genuine semidirect-product hom to the SAME elementary C2 group.
Only the additive factor is required to survive the projective quotient. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGSymplecticRankTwoSiegelExtension

open BinarySymmetricSquareAction CFSGSymplecticSerreMatrices
open CFSGSymplecticRankTwoSiegelEmbedding
variable (K : Type) [Field K]

/-- This is the actual linear congruence action with additive coordinates
written multiplicatively for the semidirect product. -/
def congruenceAction : GeneralLinear (K := K) →* MulAut (Multiplicative (Space (K := K))) where
  toFun A :=
    { toFun s := Multiplicative.ofAdd ((congruence A) s.toAdd)
      invFun s := Multiplicative.ofAdd ((congruence A).symm s.toAdd)
      left_inv s := by
        apply Multiplicative.toAdd.injective
        exact (congruence A).symm_apply_apply s.toAdd
      right_inv s := by
        apply Multiplicative.toAdd.injective
        exact (congruence A).apply_symm_apply s.toAdd
      map_mul' s t := by
        apply Multiplicative.toAdd.injective
        exact (congruence A).map_add s.toAdd t.toAdd }
  map_one' := by
    apply MulEquiv.ext
    intro s
    apply Multiplicative.toAdd.injective
    change (congruence 1) s.toAdd = s.toAdd
    rw [map_one]
    rfl
  map_mul' A B := by
    apply MulEquiv.ext
    intro s
    apply Multiplicative.toAdd.injective
    change (congruence (A * B)) s.toAdd = (congruence A) ((congruence B) s.toAdd)
    rw [map_mul]
    rfl

@[simp] theorem congruenceAction_apply (A : GeneralLinear (K := K))
    (s : Multiplicative (Space (K := K))) :
    congruenceAction K A s = Multiplicative.ofAdd (congruenceLinearMap A s.toAdd) := rfl

theorem upperHom_congruenceAction (A : GeneralLinear (K := K))
    (s : Multiplicative (Space (K := K))) :
    upperHom K (congruenceAction K A s) =
      CFSGSymplecticGeneralLinearDouble.doubleIntoElementary K 2 A * upperHom K s *
        (CFSGSymplecticGeneralLinearDouble.doubleIntoElementary K 2 A)⁻¹ := by
  rw [congruenceAction_apply]
  exact (double_upper_conjugation K A s).symm

def extensionHom :
    Multiplicative (Space (K := K)) ⋊[congruenceAction K] GeneralLinear (K := K) →*
      elementaryRootGroup K 2 :=
  SemidirectProduct.lift (upperHom K)
    (CFSGSymplecticGeneralLinearDouble.doubleIntoElementary K 2)
    (fun A => MonoidHom.ext (fun s => upperHom_congruenceAction K A s))

@[simp] theorem extensionHom_inl (s : Multiplicative (Space (K := K))) :
    extensionHom K (SemidirectProduct.inl s) = upperHom K s := by
  simp only [extensionHom, SemidirectProduct.lift_inl]

def projectiveExtensionHom [CharP K 2] :
    Multiplicative (Space (K := K)) ⋊[congruenceAction K] GeneralLinear (K := K) →*
      elementaryProjective K 2 :=
  (binaryProjectiveEquiv K 1).toMonoidHom.comp (extensionHom K)

@[simp] theorem projectiveExtensionHom_inl [CharP K 2]
    (s : Multiplicative (Space (K := K))) :
    projectiveExtensionHom K (SemidirectProduct.inl s) = projectiveUpperHom K s := by
  change binaryProjectiveEquiv K 1 (extensionHom K (SemidirectProduct.inl s)) = _
  rw [extensionHom_inl]
  rfl

end SymmetricSubgroupAsymptotics.CFSGSymplecticRankTwoSiegelExtension
