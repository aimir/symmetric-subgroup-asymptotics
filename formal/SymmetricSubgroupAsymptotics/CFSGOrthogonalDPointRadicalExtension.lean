import SymmetricSubgroupAsymptotics.CFSGOrthogonalDPointRadicalNormalizer
import Mathlib.GroupTheory.SemidirectProduct

/-! The SAME natural D tail acts on the whole additive point radical.
Their actual conjugation gives a hom from the literal semidirect product
into the literal elementary group and its central quotient. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDPointRadicalExtension

open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDPointRadicalHom
open CFSGOrthogonalDPointRadicalNormalizer CFSGOrthogonalDIndexPositiveSpace
open CFSGOrthogonalDIndexTailCoordinates
variable (K : Type) [Field K] (s : ℕ)

def tailAction : elementaryRootGroup K (s + 2) →*
    MulAut (Multiplicative (Index (s + 2) → K)) where
  toFun g := {
    toFun z := Multiplicative.ofAdd (naturalLinearHom K (s + 2) g z.toAdd)
    invFun z := Multiplicative.ofAdd ((naturalLinearHom K (s + 2) g).symm z.toAdd)
    left_inv z := by
      apply Multiplicative.toAdd.injective
      exact (naturalLinearHom K (s + 2) g).symm_apply_apply z.toAdd
    right_inv z := by
      apply Multiplicative.toAdd.injective
      exact (naturalLinearHom K (s + 2) g).apply_symm_apply z.toAdd
    map_mul' z t := by
      apply Multiplicative.toAdd.injective
      exact (naturalLinearHom K (s + 2) g).map_add z.toAdd t.toAdd }
  map_one' := by
    apply MulEquiv.ext
    intro z
    apply Multiplicative.toAdd.injective
    change naturalLinearHom K (s + 2) 1 z.toAdd = z.toAdd
    rw [map_one]
    rfl
  map_mul' g h := by
    apply MulEquiv.ext
    intro z
    apply Multiplicative.toAdd.injective
    change naturalLinearHom K (s + 2) (g * h) z.toAdd =
      naturalLinearHom K (s + 2) g (naturalLinearHom K (s + 2) h z.toAdd)
    rw [map_mul]
    rfl

@[simp] theorem tailAction_apply (g : elementaryRootGroup K (s + 2))
    (z : Multiplicative (Index (s + 2) → K)) :
    tailAction K s g z = Multiplicative.ofAdd (naturalLinearHom K (s + 2) g z.toAdd) := rfl

theorem radicalHom_tailAction (g : elementaryRootGroup K (s + 2))
    (z : Multiplicative (Index (s + 2) → K)) :
    radicalHom K s (tailAction K s g z) =
      tailElementaryHom K (s + 2) (by omega) g * radicalHom K s z *
        (tailElementaryHom K (s + 2) (by omega) g)⁻¹ :=
  radical_tail_conjugation K s g z.toAdd

def extensionHom :
    Multiplicative (Index (s + 2) → K) ⋊[tailAction K s]
      elementaryRootGroup K (s + 2) →* elementaryRootGroup K (s + 3) :=
  SemidirectProduct.lift (radicalHom K s) (tailElementaryHom K (s + 2) (by omega))
    (fun g => MonoidHom.ext (fun z => radicalHom_tailAction K s g z))

@[simp] theorem extensionHom_inl (z : Multiplicative (Index (s + 2) → K)) :
    extensionHom K s (SemidirectProduct.inl z) = radicalHom K s z := by
  simp only [extensionHom, SemidirectProduct.lift_inl]

def projectiveExtensionHom :
    Multiplicative (Index (s + 2) → K) ⋊[tailAction K s]
      elementaryRootGroup K (s + 2) →* elementaryProjective K (s + 3) :=
  (QuotientGroup.mk' (Subgroup.center (elementaryRootGroup K (s + 3)))).comp (extensionHom K s)

@[simp] theorem projectiveExtensionHom_inl (z : Multiplicative (Index (s + 2) → K)) :
    projectiveExtensionHom K s (SemidirectProduct.inl z) = projectiveRadicalHom K s z := by
  change QuotientGroup.mk' _ (extensionHom K s (SemidirectProduct.inl z)) = _
  rw [extensionHom_inl]
  rfl

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDPointRadicalExtension
