import SymmetricSubgroupAsymptotics.BlockKernelClassBound
import Mathlib.GroupTheory.SemidirectProduct

/-! A compatible map of actual semidirect products has an exact kernel
cardinality: its underlying kernel is the product of the two original
kernels. Restricting that SAME map to an actual subgroup retains its
actual image and needs no splitting of the source subgroup. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SemidirectQuotientKernelCardinality

variable {N C V D : Type*} [Group N] [Group C] [Group V] [Group D]
    (φ : C →* MulAut N) (ψ : D →* MulAut V)
    (π : N →* V) (ρ : C →* D)
    (hcompat : ∀ c : C,
      π.comp (φ c).toMonoidHom=(ψ (ρ c)).toMonoidHom.comp π)

def quotientHom : N ⋊[φ] C →* V ⋊[ψ] D :=
  SemidirectProduct.map π ρ hcompat

def kernelEquiv : (quotientHom φ ψ π ρ hcompat).ker ≃ π.ker×ρ.ker where
  toFun x :=
    (⟨x.val.left,congrArg SemidirectProduct.left x.property⟩,
      ⟨x.val.right,congrArg SemidirectProduct.right x.property⟩)
  invFun x := ⟨⟨x.1.val,x.2.val⟩,by
    apply SemidirectProduct.ext
    · exact x.1.property
    · exact x.2.property⟩
  left_inv x := by
    apply Subtype.ext
    apply SemidirectProduct.ext <;> rfl
  right_inv x := by
    apply Prod.ext <;> apply Subtype.ext <;> rfl

theorem kernel_card : Nat.card (quotientHom φ ψ π ρ hcompat).ker=
    Nat.card π.ker*Nat.card ρ.ker := by
  rw [Nat.card_congr (kernelEquiv φ ψ π ρ hcompat),Nat.card_prod]

local instance finiteSemidirect [Finite N] [Finite C] : Finite (N ⋊[φ] C) :=
  Finite.of_equiv (N×C) SemidirectProduct.equivProd.symm

theorem restricted_kernel_card_le [Finite N] [Finite C]
    (A : Subgroup (N ⋊[φ] C)) :
    Nat.card (((quotientHom φ ψ π ρ hcompat).comp A.subtype).ker)≤
      Nat.card π.ker*Nat.card ρ.ker := by
  let F := quotientHom φ ψ π ρ hcompat
  let f : (F.comp A.subtype).ker → F.ker := fun x => ⟨x.val.val,x.property⟩
  have hf : Function.Injective f := by
    intro x y he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : F.ker => z.val) he
  exact (Nat.card_le_card_of_injective f hf).trans_eq (kernel_card φ ψ π ρ hcompat)

theorem subgroup_class_card_le_kernel_mul_range [Finite N] [Finite C]
    (A : Subgroup (N ⋊[φ] C)) :
    Nat.card (ConjClasses A)≤(Nat.card π.ker*Nat.card ρ.ker)*
      Nat.card (ConjClasses (((quotientHom φ ψ π ρ hcompat).comp A.subtype).range)) := by
  let F := (quotientHom φ ψ π ρ hcompat).comp A.subtype
  have hk : Nat.card (ConjClasses F.ker)≤Nat.card π.ker*Nat.card ρ.ker :=
    (Nat.card_le_card_of_surjective ConjClasses.mk ConjClasses.mk_surjective).trans
      (restricted_kernel_card_le φ ψ π ρ hcompat A)
  exact (conjugacyClass_card_le_kernel_mul_range F).trans
    (Nat.mul_le_mul_right _ hk)

end SymmetricSubgroupAsymptotics.SemidirectQuotientKernelCardinality
