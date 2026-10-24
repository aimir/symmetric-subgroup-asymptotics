import SymmetricSubgroupAsymptotics.CFSGSymplecticHeisenbergTail
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.GroupTheory.SemidirectProduct

/-! The actual tail normalizer supplies an action on the original
Heisenberg coordinates, and hence a literal semidirect-product map to
the original elementary C2 group and its actual central quotient.
The action is transported through an injective actual matrix range;
no abstract parabolic or extension recognition is an input. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticHeisenbergExtension

open CFSGHeisenbergCoordinateGroup CFSGSymplecticSerreMatrices
open CFSGSymplecticHeisenbergEmbedding CFSGSymplecticHeisenbergTail
open CFSGTypeASLTwoWeyl
variable (K : Type) [Field K]

theorem elementaryHom_injective (hTwo : (2 : K) ≠ 0) :
    Function.Injective (elementaryHom K) := by
  intro g h he
  apply projectiveHom_injective K hTwo
  exact congrArg (QuotientGroup.mk' (Subgroup.center (elementaryRootGroup K 2))) he

def rangeEquiv (hTwo : (2 : K) ≠ 0) : Element K 1 ≃* (elementaryHom K).range :=
  MonoidHom.ofInjective (elementaryHom_injective K hTwo)

def tailIntoNormalizer (hTwo : (2 : K) ≠ 0) :
    SL2 (F := K) →* Subgroup.normalizer
      ((elementaryHom K).range : Set (elementaryRootGroup K 2)) where
  toFun A := ⟨tailHom K A, tailHom_range_normalizes K hTwo ⟨A, rfl⟩⟩
  map_one' := Subtype.ext ((tailHom K).map_one)
  map_mul' A B := Subtype.ext ((tailHom K).map_mul A B)

def tailAction (hTwo : (2 : K) ≠ 0) : SL2 (F := K) →* MulAut (Element K 1) :=
  (MulAut.congr (rangeEquiv K hTwo).symm).toMonoidHom.comp
    ((elementaryHom K).range.normalizerMonoidHom.comp (tailIntoNormalizer K hTwo))

theorem elementaryHom_tailAction (hTwo : (2 : K) ≠ 0)
    (A : SL2 (F := K)) (g : Element K 1) :
    elementaryHom K (tailAction K hTwo A g) =
      tailHom K A * elementaryHom K g * (tailHom K A)⁻¹ := by
  change ((rangeEquiv K hTwo)
    ((rangeEquiv K hTwo).symm
      (((elementaryHom K).range.normalizerMonoidHom (tailIntoNormalizer K hTwo A))
        (rangeEquiv K hTwo g)))).val = _
  rw [(rangeEquiv K hTwo).apply_symm_apply]
  rfl

theorem tailAction_apply (hTwo : (2 : K) ≠ 0)
    (A : SL2 (F := K)) (g : Element K 1) :
    tailAction K hTwo A g = transform K A g := by
  apply elementaryHom_injective K hTwo
  exact (elementaryHom_tailAction K hTwo A g).trans (tailHom_conjugation K hTwo A g)

def extensionHom (hTwo : (2 : K) ≠ 0) :
    Element K 1 ⋊[tailAction K hTwo] SL2 (F := K) →* elementaryRootGroup K 2 :=
  SemidirectProduct.lift (elementaryHom K) (tailHom K) (fun A => by
    exact MonoidHom.ext (fun g => elementaryHom_tailAction K hTwo A g))

theorem extensionHom_inl (hTwo : (2 : K) ≠ 0) (g : Element K 1) :
    extensionHom K hTwo (SemidirectProduct.inl g) = elementaryHom K g := by
  simp only [extensionHom, SemidirectProduct.lift_inl]

def projectiveExtensionHom (hTwo : (2 : K) ≠ 0) :
    Element K 1 ⋊[tailAction K hTwo] SL2 (F := K) →* elementaryProjective K 2 :=
  (QuotientGroup.mk' (Subgroup.center (elementaryRootGroup K 2))).comp (extensionHom K hTwo)

theorem projectiveExtensionHom_inl (hTwo : (2 : K) ≠ 0) (g : Element K 1) :
    projectiveExtensionHom K hTwo (SemidirectProduct.inl g) = projectiveHom K g := by
  change QuotientGroup.mk' (Subgroup.center (elementaryRootGroup K 2))
    (extensionHom K hTwo (SemidirectProduct.inl g)) = _
  rw [extensionHom_inl]
  rfl

end SymmetricSubgroupAsymptotics.CFSGSymplecticHeisenbergExtension
