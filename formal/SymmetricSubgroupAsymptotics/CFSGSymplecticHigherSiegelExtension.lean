import SymmetricSubgroupAsymptotics.CFSGSymplecticHigherSiegelEmbedding
import Mathlib.GroupTheory.SemidirectProduct

/-! The actual all-rank GL congruence action and actual upper-shear
conjugation give a literal semidirect-product hom into the SAME
elementary symplectic group and its original central quotient. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGSymplecticHigherSiegelExtension

open SymmetricMatrixCongruenceAction CFSGSymplecticSerreMatrices
open CFSGSymplecticHigherSiegelEmbedding
variable (K : Type) [Field K] (m : ℕ) (hm : 0 < m)

def congruenceAction : GeneralLinear (K := K) (m + 1) →*
    MulAut (Multiplicative (Space (K := K) (m + 1))) where
  toFun A := {
    toFun s := Multiplicative.ofAdd ((congruence (m + 1) A) s.toAdd)
    invFun s := Multiplicative.ofAdd ((congruence (m + 1) A).symm s.toAdd)
    left_inv s := by
      apply Multiplicative.toAdd.injective
      exact (congruence (m + 1) A).symm_apply_apply s.toAdd
    right_inv s := by
      apply Multiplicative.toAdd.injective
      exact (congruence (m + 1) A).apply_symm_apply s.toAdd
    map_mul' s t := by
      apply Multiplicative.toAdd.injective
      exact (congruence (m + 1) A).map_add s.toAdd t.toAdd }
  map_one' := by
    apply MulEquiv.ext
    intro s
    apply Multiplicative.toAdd.injective
    change (congruence (m + 1) 1) s.toAdd = s.toAdd
    rw [map_one]
    rfl
  map_mul' A B := by
    apply MulEquiv.ext
    intro s
    apply Multiplicative.toAdd.injective
    change (congruence (m + 1) (A * B)) s.toAdd =
      (congruence (m + 1) A) ((congruence (m + 1) B) s.toAdd)
    rw [map_mul]
    rfl

@[simp] theorem congruenceAction_apply (A : GeneralLinear (K := K) (m + 1))
    (s : Multiplicative (Space (K := K) (m + 1))) :
    congruenceAction K m A s =
      Multiplicative.ofAdd (congruenceLinearMap (m + 1) A s.toAdd) := rfl

theorem upperHom_congruenceAction (A : GeneralLinear (K := K) (m + 1))
    (s : Multiplicative (Space (K := K) (m + 1))) :
    upperHom K m hm (congruenceAction K m A s) =
      CFSGSymplecticGeneralLinearDouble.doubleIntoElementary K (m + 1) A * upperHom K m hm s *
        (CFSGSymplecticGeneralLinearDouble.doubleIntoElementary K (m + 1) A)⁻¹ := by
  rw [congruenceAction_apply]
  exact (double_upper_conjugation K m hm A s).symm

def extensionHom :
    Multiplicative (Space (K := K) (m + 1)) ⋊[congruenceAction K m]
      GeneralLinear (K := K) (m + 1) →* elementaryRootGroup K (m + 1) :=
  SemidirectProduct.lift (upperHom K m hm)
    (CFSGSymplecticGeneralLinearDouble.doubleIntoElementary K (m + 1))
    (fun A => MonoidHom.ext (fun s => upperHom_congruenceAction K m hm A s))

@[simp] theorem extensionHom_inl (s : Multiplicative (Space (K := K) (m + 1))) :
    extensionHom K m hm (SemidirectProduct.inl s) = upperHom K m hm s := by
  simp only [extensionHom, SemidirectProduct.lift_inl]

def projectiveExtensionHom [CharP K 2] :
    Multiplicative (Space (K := K) (m + 1)) ⋊[congruenceAction K m]
      GeneralLinear (K := K) (m + 1) →* elementaryProjective K (m + 1) :=
  (binaryProjectiveEquiv K m).toMonoidHom.comp (extensionHom K m hm)

@[simp] theorem projectiveExtensionHom_inl [CharP K 2]
    (s : Multiplicative (Space (K := K) (m + 1))) :
    projectiveExtensionHom K m hm (SemidirectProduct.inl s) = projectiveUpperHom K m hm s := by
  change binaryProjectiveEquiv K m (extensionHom K m hm (SemidirectProduct.inl s)) = _
  rw [extensionHom_inl]
  rfl

end SymmetricSubgroupAsymptotics.CFSGSymplecticHigherSiegelExtension
