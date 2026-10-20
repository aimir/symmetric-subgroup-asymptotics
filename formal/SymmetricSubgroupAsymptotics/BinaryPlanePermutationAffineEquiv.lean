import SymmetricSubgroupAsymptotics.BinaryPlaneFunctions
import SymmetricSubgroupAsymptotics.LinearSemidirectCoprimeSocleBounds

/-! Every permutation of the four binary-plane points has its literal
translation and linear part. This gives a concrete affine equivalence
without a primitive-group classification or a choice of abstract kernel. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryPlanePermutationAffineEquiv

open SemidirectProduct

abbrev Plane := Fin 2 → ZMod 2
abbrev Linear := Plane ≃ₗ[ZMod 2] Plane

def centered (σ : Equiv.Perm Plane) : Plane ≃+ Plane :=
  IsAddKleinFour.addEquiv (σ.trans (Equiv.addRight (σ 0)))
    (by change σ 0 + σ 0 = 0; exact binaryVector_add_self _)

def linear (σ : Equiv.Perm Plane) : Linear :=
  { centered σ with map_smul' := ZMod.map_smul (centered σ).toAddMonoidHom }

@[simp] theorem linear_apply (σ : Equiv.Perm Plane) (v : Plane) :
    linear σ v = σ v + σ 0 := rfl

def linearPart : Equiv.Perm Plane →* Linear where
  toFun := linear
  map_one' := by
    apply LinearEquiv.ext
    intro v
    change v + 0 = v
    exact add_zero v
  map_mul' σ τ := by
    apply LinearEquiv.ext
    intro v
    change σ (τ v) + σ (τ 0) = σ (τ v + τ 0) + σ 0
    rw [binaryPlane_permutation_affine]
    simp only [add_assoc,binaryVector_add_self,add_zero]

abbrev Model := LinearSemidirectCoprimeSocleBounds.Model (MonoidHom.id Linear)

def affineMap : Equiv.Perm Plane →* Model where
  toFun σ := ⟨Multiplicative.ofAdd (σ 0),linearPart σ⟩
  map_one' := by
    apply SemidirectProduct.ext
    · rfl
    · exact linearPart.map_one
  map_mul' σ τ := by
    apply SemidirectProduct.ext
    · apply Multiplicative.toAdd.injective
      change σ (τ 0) = σ 0 + (σ (τ 0) + σ 0)
      simp only [add_left_comm (σ 0),binaryVector_add_self,add_zero]
    · exact linearPart.map_mul σ τ

@[simp] theorem affineMap_left (σ : Equiv.Perm Plane) :
    (affineMap σ).left.toAdd = σ 0 := rfl

@[simp] theorem affineMap_right (σ : Equiv.Perm Plane) :
    (affineMap σ).right = linearPart σ := rfl

theorem affineMap_injective : Function.Injective affineMap := by
  intro σ τ h
  have h0 : σ 0 = τ 0 := congrArg (fun g : Model => g.left.toAdd) h
  apply Equiv.ext
  intro v
  have hv : σ v + σ 0 = τ v + τ 0 :=
    congrArg (fun g : Model => g.right v) h
  rw [h0] at hv
  exact add_right_cancel hv

def permutation (g : Model) : Equiv.Perm Plane where
  toFun v := g.left.toAdd + g.right v
  invFun v := g.right.symm (v-g.left.toAdd)
  left_inv v := by simp only [add_sub_cancel_left,LinearEquiv.symm_apply_apply]
  right_inv v := by
    change g.left.toAdd + g.right (g.right.symm (v-g.left.toAdd)) = v
    rw [LinearEquiv.apply_symm_apply,add_comm,sub_add_cancel]

theorem affineMap_permutation (g : Model) : affineMap (permutation g) = g := by
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    change g.left.toAdd + g.right 0 = g.left.toAdd
    rw [map_zero,add_zero]
  · apply LinearEquiv.ext
    intro v
    change (g.left.toAdd + g.right v) + (g.left.toAdd + g.right 0) = g.right v
    rw [map_zero,add_zero]
    rw [add_right_comm,binaryVector_add_self,zero_add]

theorem affineMap_surjective : Function.Surjective affineMap :=
  fun g => ⟨permutation g,affineMap_permutation g⟩

def equiv : Equiv.Perm Plane ≃* Model :=
  MulEquiv.ofBijective affineMap ⟨affineMap_injective,affineMap_surjective⟩

theorem linearPart_surjective : Function.Surjective linearPart := by
  intro L
  obtain ⟨σ,hσ⟩ := affineMap_surjective (inr L)
  exact ⟨σ,congrArg SemidirectProduct.right hσ⟩

end SymmetricSubgroupAsymptotics.BinaryPlanePermutationAffineEquiv

end
