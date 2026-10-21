import SymmetricSubgroupAsymptotics.BinaryPairDerivedZeroLifts
import SymmetricSubgroupAsymptotics.PermutationBinaryFourAugmentation

/-! An original augmentation flip kernel makes the retained affine
quotient action trivial. Every derived actual top element therefore has
an actual zero-offset lift; the other offsets remain unrestricted. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
variable {X : Type} {w : ℕ} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin w))

theorem affineQuotientRepresentation_trivial_of_kernel_augmentation
    (hK : F.kernelSpace=PermutationAugmentation.space (ZMod 2) (Fin w)) :
    ∀ (t : F.top.range) a,F.affineQuotientRepresentation t a=a := by
  intro t a
  obtain ⟨v,rfl⟩ := F.kernelSpace.mkQ_surjective a
  change F.kernelSpace.mkQ
    (permutationFunctionRepresentation (ZMod 2) F.top.range (Fin w) t v)=F.kernelSpace.mkQ v
  apply sub_eq_zero.mp
  rw [←map_sub]
  apply (Submodule.Quotient.mk_eq_zero F.kernelSpace).mpr
  rw [hK]
  change PermutationAugmentation.coordinateSum (ZMod 2) (Fin w)
    (permutationFunctionRepresentation (ZMod 2) F.top.range (Fin w) t v-v)=0
  rw [map_sub,PermutationAugmentation.coordinateSum_permutation,sub_self]

theorem augmentation_affineClass_eq_zero_of_derived_top
    (hK : F.kernelSpace=PermutationAugmentation.space (ZMod 2) (Fin w))
    (t : F.top.range) (ht : t∈commutator F.top.range) : F.affineClass t=0 :=
  F.affineClass_eq_zero_of_derived_top
    (F.affineQuotientRepresentation_trivial_of_kernel_augmentation hK) t ht

end SymmetricSubgroupAsymptotics.BinaryPairFrame
