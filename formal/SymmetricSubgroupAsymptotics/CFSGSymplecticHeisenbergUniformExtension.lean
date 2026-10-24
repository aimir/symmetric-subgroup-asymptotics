import SymmetricSubgroupAsymptotics.CFSGSymplecticHeisenbergUniformNormalizer
import Mathlib.GroupTheory.SemidirectProduct

/-! The actual tail normalizer induces an actual action on the original
coordinate Heisenberg group and a literal semidirect-product map into
the SAME elementary group and its SAME projective central quotient. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGSymplecticHeisenbergUniformExtension

open CFSGHeisenbergCoordinateGroup CFSGSymplecticSerreMatrices
open CFSGSymplecticHeisenbergUniformEmbedding CFSGSymplecticUniformTail
open CFSGSymplecticHeisenbergUniformNormalizer CFSGSymplecticHeisenbergVectorAction
variable (K : Type) [Field K]

def rangeEquiv (m : ℕ) (hm : 0 < m) (hTwo : (2 : K) ≠ 0) :
    Element K m ≃* (elementaryHom K m hm).range :=
  MonoidHom.ofInjective (elementaryHom_injective K m hm hTwo)

def tailIntoNormalizer (m : ℕ) (hm : 0 < m) (hTwo : (2 : K) ≠ 0) :
    elementaryRootGroup K m →* Subgroup.normalizer
      ((elementaryHom K m hm).range : Set (elementaryRootGroup K (m + 1))) where
  toFun A := ⟨tailHom K m A, tailHom_range_normalizes K m hm hTwo ⟨A, rfl⟩⟩
  map_one' := Subtype.ext ((tailHom K m).map_one)
  map_mul' A B := Subtype.ext ((tailHom K m).map_mul A B)

def tailAction (m : ℕ) (hm : 0 < m) (hTwo : (2 : K) ≠ 0) :
    elementaryRootGroup K m →* MulAut (Element K m) :=
  (MulAut.congr (rangeEquiv K m hm hTwo).symm).toMonoidHom.comp
    ((elementaryHom K m hm).range.normalizerMonoidHom.comp (tailIntoNormalizer K m hm hTwo))

theorem elementaryHom_tailAction (m : ℕ) (hm : 0 < m) (hTwo : (2 : K) ≠ 0)
    (A : elementaryRootGroup K m) (g : Element K m) :
    elementaryHom K m hm (tailAction K m hm hTwo A g) =
      tailHom K m A * elementaryHom K m hm g * (tailHom K m A)⁻¹ := by
  change ((rangeEquiv K m hm hTwo)
    ((rangeEquiv K m hm hTwo).symm
      (((elementaryHom K m hm).range.normalizerMonoidHom (tailIntoNormalizer K m hm hTwo A))
        (rangeEquiv K m hm hTwo g)))).val = _
  rw [(rangeEquiv K m hm hTwo).apply_symm_apply]
  rfl

theorem tailAction_apply (m : ℕ) (hm : 0 < m) (hTwo : (2 : K) ≠ 0)
    (A : elementaryRootGroup K m) (g : Element K m) :
    tailAction K m hm hTwo A g = transform K m A g := by
  apply elementaryHom_injective K m hm hTwo
  exact (elementaryHom_tailAction K m hm hTwo A g).trans (tailHom_conjugation K m hm hTwo A g)

local instance extensionVectorActionInstance (m : ℕ) :
    MulAction (elementaryRootGroup K m) ((Fin m → K) × (Fin m → K)) := vectorAction K m

theorem coordinate_action (m : ℕ) (hm : 0 < m) (hTwo : (2 : K) ≠ 0)
    (A : elementaryRootGroup K m) (g : Element K m) :
    ((tailAction K m hm hTwo A g).a, (tailAction K m hm hTwo A g).b) = A • (g.a, g.b) := by
  rw [tailAction_apply]
  exact transform_vector K m A g

def extensionHom (m : ℕ) (hm : 0 < m) (hTwo : (2 : K) ≠ 0) :
    Element K m ⋊[tailAction K m hm hTwo] elementaryRootGroup K m →*
      elementaryRootGroup K (m + 1) :=
  SemidirectProduct.lift (elementaryHom K m hm) (tailHom K m) (fun A => by
    exact MonoidHom.ext (fun g => elementaryHom_tailAction K m hm hTwo A g))

theorem extensionHom_inl (m : ℕ) (hm : 0 < m) (hTwo : (2 : K) ≠ 0) (g : Element K m) :
    extensionHom K m hm hTwo (SemidirectProduct.inl g) = elementaryHom K m hm g := by
  simp only [extensionHom, SemidirectProduct.lift_inl]

def projectiveExtensionHom (m : ℕ) (hm : 0 < m) (hTwo : (2 : K) ≠ 0) :
    Element K m ⋊[tailAction K m hm hTwo] elementaryRootGroup K m →*
      elementaryProjective K (m + 1) :=
  (QuotientGroup.mk' (Subgroup.center (elementaryRootGroup K (m + 1)))).comp
    (extensionHom K m hm hTwo)

theorem projectiveExtensionHom_inl (m : ℕ) (hm : 0 < m) (hTwo : (2 : K) ≠ 0) (g : Element K m) :
    projectiveExtensionHom K m hm hTwo (SemidirectProduct.inl g) = projectiveHom K m hm g := by
  change QuotientGroup.mk' (Subgroup.center (elementaryRootGroup K (m + 1)))
    (extensionHom K m hm hTwo (SemidirectProduct.inl g)) = _
  rw [extensionHom_inl]
  rfl

end SymmetricSubgroupAsymptotics.CFSGSymplecticHeisenbergUniformExtension
