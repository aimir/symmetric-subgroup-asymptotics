import SymmetricSubgroupAsymptotics.BinaryPairSplitAffineRows
import SymmetricSubgroupAsymptotics.BinaryPairCoordinateSubgroups
import SymmetricSubgroupAsymptotics.LinearSemidirectProperNormalF

/-! An injective affine chart for every original pair action, including
nonsplit extensions and all actual offsets. The ambient vector space is
used only as coordinates; it is not asserted to be the original kernel. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
open SemidirectProduct
open LinearSemidirectCoprimeSocleBounds
local instance ambientAffineEmbedding_primeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
variable {X : Type} {w : ℕ} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin w))

def ambientAffineLinearAction :
    F.top.range →* ((Fin w → ZMod 2) ≃ₗ[ZMod 2] (Fin w → ZMod 2)) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin w → ZMod 2)).toMonoidHom.comp
    (permutationFunctionRepresentation (ZMod 2) F.top.range (Fin w)).asGroupHom

abbrev AmbientAffineModel := Model F.ambientAffineLinearAction

def ambientAffineEmbedding : U →* F.AmbientAffineModel where
  toFun u := ⟨Multiplicative.ofAdd (F.affineTranslation u),F.top.rangeRestrict u⟩
  map_one' := by
    apply SemidirectProduct.ext
    · exact congrArg Multiplicative.ofAdd F.affineTranslation_one
    · exact map_one F.top.rangeRestrict
  map_mul' u v := by
    apply SemidirectProduct.ext
    · apply Multiplicative.toAdd.injective
      change F.affineTranslation (u*v) =
        F.affineTranslation u +
          permutationFunctionRepresentation (ZMod 2) F.top.range (Fin w)
            (F.top.rangeRestrict u) (F.affineTranslation v)
      rw [F.affineTranslation_mul,add_comm]
    · exact map_mul F.top.rangeRestrict u v

theorem ambientAffineEmbedding_injective : Function.Injective F.ambientAffineEmbedding := by
  intro u v h
  apply F.affineCoordinates_injective
  exact Prod.ext (congrArg (fun z : F.AmbientAffineModel => z.right) h)
    (congrArg (fun z : F.AmbientAffineModel => z.left.toAdd) h)

@[simp] theorem ambientAffineEmbedding_right (u : U) :
    (F.ambientAffineEmbedding u).right = F.top.rangeRestrict u := rfl
@[simp] theorem ambientAffineEmbedding_left (u : U) :
    (F.ambientAffineEmbedding u).left.toAdd = F.affineTranslation u := rfl

theorem ambientAffineEmbedding_kernel (k : F.top.ker) :
    F.ambientAffineEmbedding k.val = inl (Multiplicative.ofAdd (F.bits k)) := by
  apply SemidirectProduct.ext
  · exact congrArg Multiplicative.ofAdd (F.affineTranslation_kernel k)
  · exact Subtype.ext k.property

/-- The exact preimage of an ambient translation subspace is the original
physical subgroup, with no additional flip vectors introduced. -/
theorem ambientAffine_translation_preimage (D : Submodule (ZMod 2) (Fin w → ZMod 2)) :
    (translationSpace F.ambientAffineLinearAction D).comap F.ambientAffineEmbedding =
      F.coordinateSubgroup D := by
  ext u
  constructor
  · rintro ⟨ht,ha⟩
    have hu : u ∈ F.top.ker := congrArg Subtype.val ht
    let k : F.top.ker := ⟨u,hu⟩
    apply (F.kernel_mem_coordinateSubgroup D k).mpr
    rwa [← F.affineTranslation_kernel k]
  · rintro ⟨k,hk,rfl⟩
    change F.ambientAffineEmbedding k.val ∈ translationSpace F.ambientAffineLinearAction D
    rw [F.ambientAffineEmbedding_kernel]
    exact ⟨rfl,hk⟩

end SymmetricSubgroupAsymptotics.BinaryPairFrame
