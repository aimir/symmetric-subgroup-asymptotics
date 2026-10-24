import SymmetricSubgroupAsymptotics.CFSGOrthogonalBPointRadicalNormalizer
import Mathlib.GroupTheory.SemidirectProduct

/-! The SAME natural odd-B tail acts on the whole additive point radical.
Their actual conjugation gives a hom from the literal semidirect product
into the literal elementary group and its central quotient. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBPointRadicalExtension

open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBPointRadicalHom
open CFSGOrthogonalBPointRadicalNormalizer CFSGOrthogonalBOddPoleShearElementary
open CFSGOrthogonalBTailCoordinates
variable (K : Type) [Field K] [Finite K] (s : ℕ)

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

omit [Finite K] in
@[simp] theorem tailAction_apply (g : elementaryRootGroup K (s + 2))
    (z : Multiplicative (Index (s + 2) → K)) :
    tailAction K s g z = Multiplicative.ofAdd (naturalLinearHom K (s + 2) g z.toAdd) := rfl

theorem radicalHom_tailAction (h2 : (2 : K) ≠ 0) (g : elementaryRootGroup K (s + 2))
    (z : Multiplicative (Index (s + 2) → K)) :
    radicalHom K h2 s (tailAction K s g z) =
      tailElementaryHom K (s + 2) g * radicalHom K h2 s z *
        (tailElementaryHom K (s + 2) g)⁻¹ :=
  radical_tail_conjugation K h2 s g z.toAdd

def extensionHom (h2 : (2 : K) ≠ 0) :
    Multiplicative (Index (s + 2) → K) ⋊[tailAction K s]
      elementaryRootGroup K (s + 2) →* elementaryRootGroup K (s + 3) :=
  SemidirectProduct.lift (radicalHom K h2 s) (tailElementaryHom K (s + 2))
    (fun g => MonoidHom.ext (fun z => radicalHom_tailAction K s h2 g z))

@[simp] theorem extensionHom_inl (h2 : (2 : K) ≠ 0) (z : Multiplicative (Index (s + 2) → K)) :
    extensionHom K s h2 (SemidirectProduct.inl z) = radicalHom K h2 s z := by
  simp only [extensionHom, SemidirectProduct.lift_inl]

def projectiveExtensionHom (h2 : (2 : K) ≠ 0) :
    Multiplicative (Index (s + 2) → K) ⋊[tailAction K s]
      elementaryRootGroup K (s + 2) →* elementaryProjective K (s + 3) :=
  (QuotientGroup.mk' (Subgroup.center (elementaryRootGroup K (s + 3)))).comp (extensionHom K s h2)

@[simp] theorem projectiveExtensionHom_inl (h2 : (2 : K) ≠ 0) (z : Multiplicative (Index (s + 2) → K)) :
    projectiveExtensionHom K s h2 (SemidirectProduct.inl z) = projectiveRadicalHom K h2 s z := by
  change QuotientGroup.mk' _ (extensionHom K s h2 (SemidirectProduct.inl z)) = _
  rw [extensionHom_inl]
  rfl

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBPointRadicalExtension
