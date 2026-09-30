import SymmetricSubgroupAsymptotics.BinaryPairAffineCoboundary

/-!
# Recognising a literal split pair action

If every element of an original pair action has translation in its actual
correlated kernel, then the original permutation subgroup is exactly the
physical split action.  The reverse inclusion uses the reversible kernel
chart, so no cardinal comparison or ambient independent-flip group enters.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X I : Type} {U : Subgroup (Equiv.Perm X)} (F : BinaryPairFrame U I)

/-- Original elements whose affine translation already lies in the actual
correlated kernel form a subgroup. -/
def translationKernelSubgroup : Subgroup U where
  carrier := {u | F.affineTranslation u∈F.kernelSpace}
  one_mem' := by
    change F.affineTranslation (1 : U)∈F.kernelSpace
    rw [F.affineTranslation_one]
    exact F.kernelSpace.zero_mem
  mul_mem' := by
    intro u v hu hv
    change F.affineTranslation (u*v)∈F.kernelSpace
    change F.affineTranslation u∈F.kernelSpace at hu
    change F.affineTranslation v∈F.kernelSpace at hv
    rw [F.affineTranslation_mul]
    exact F.kernelSpace.add_mem
      (F.kernelTopPermutationSubrepresentation.apply_mem_toSubmodule _ hv) hu
  inv_mem' := by
    intro u hu
    change F.affineTranslation u∈F.kernelSpace at hu
    change F.affineTranslation u⁻¹∈F.kernelSpace
    have hm := F.affineTranslation_mul u⁻¹ u
    rw [inv_mul_cancel,F.affineTranslation_one] at hm
    have hact : permutationFunctionRepresentation (ZMod 2) F.top.range I
        (F.top.rangeRestrict u⁻¹) (F.affineTranslation u)∈F.kernelSpace :=
      F.kernelTopPermutationSubrepresentation.apply_mem_toSubmodule _ hu
    have he : F.affineTranslation u⁻¹=
        -permutationFunctionRepresentation (ZMod 2) F.top.range I
          (F.top.rangeRestrict u⁻¹) (F.affineTranslation u) := by
      exact eq_neg_of_add_eq_zero_right hm.symm
    rw [he]
    exact F.kernelSpace.neg_mem hact

/-- Vanishing of the retained affine class on the whole original source is
equivalent here to literal equality with the physical split action. -/
theorem eq_splitAffineAction_of_translation_mem
    (htranslation : ∀ u : U,F.affineTranslation u∈F.kernelSpace) :
    U=F.splitAffineAction := by
  apply le_antisymm
  · intro p hp
    let u : U := ⟨p,hp⟩
    apply Subgroup.subset_closure
    refine ⟨F.top.rangeRestrict u,F.affineTranslation u,htranslation u,?_⟩
    simpa only [u] using (F.affinePermutation_original u).symm
  · apply (Subgroup.closure_le _).mpr
    rintro p ⟨t,a,ha,rfl⟩
    obtain ⟨u,hu⟩ := F.top.rangeRestrict_surjective t
    have hd : a-F.affineTranslation u∈F.kernelSpace :=
      F.kernelSpace.sub_mem ha (htranslation u)
    obtain ⟨k,hk⟩ := hd
    change F.bits k.toMul=a-F.affineTranslation u at hk
    let v : U := (k.toMul : U)*u
    have htop : F.top v=(t : Equiv.Perm I) := by
      change F.top ((k.toMul : U)*u)=(t : Equiv.Perm I)
      rw [map_mul,k.toMul.property,one_mul]
      exact congrArg Subtype.val hu
    have hshift : F.affineTranslation v=a := by
      change F.affineTranslation ((k.toMul : U)*u)=a
      rw [F.affineTranslation_kernel_mul,hk]
      abel
    have he : F.affinePermutation (t : Equiv.Perm I) a=(v : Equiv.Perm X) := by
      rw [← F.affinePermutation_original v,htop,hshift]
    rw [he]
    exact v.property

/-- It is enough to check the retained-kernel translation condition on any
generating tuple of the original source. -/
theorem eq_splitAffineAction_of_generators
    {κ : Type} (generators : κ → U)
    (hfull : Subgroup.closure (Set.range generators)=⊤)
    (hgenerators : ∀ j,F.affineTranslation (generators j)∈F.kernelSpace) :
    U=F.splitAffineAction := by
  apply F.eq_splitAffineAction_of_translation_mem
  intro u
  have hle : Subgroup.closure (Set.range generators)≤
      F.translationKernelSubgroup := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    exact hgenerators j
  rw [hfull] at hle
  exact hle (Subgroup.mem_top u)

end SymmetricSubgroupAsymptotics.BinaryPairFrame
