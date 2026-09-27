import SymmetricSubgroupAsymptotics.BinaryPairAffineChart

/-! Exact affine commutators of original pair actions.

The denominator below is the image of the literal intersection of an
original normal subgroup with the original pair kernel. Equality in the
original quotient supplies the commutator equation; no split extension,
independent flip coordinates, or identification of the normal subgroup
with that intersection is assumed.
-/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X I : Type} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U I) (N : Subgroup U) [N.Normal]

/-- Two original lifts having the same top and the same original quotient
image differ by the literal normal-intersection flip space. -/
theorem affineTranslation_sub_mem_normalSpace (u v : U)
    (ht : F.top u=F.top v)
    (hq : QuotientGroup.mk' N u=QuotientGroup.mk' N v) :
    F.affineTranslation u-F.affineTranslation v∈
      (F.normalSpace N).map F.kernelSpace.subtype := by
  let k : F.top.ker := ⟨u*v⁻¹,by
    change F.top (u*v⁻¹)=1
    rw [map_mul,map_inv,ht,mul_inv_cancel]⟩
  have hkN : (k:U)∈N := by
    apply (QuotientGroup.eq_one_iff (u*v⁻¹)).mp
    change QuotientGroup.mk' N (u*v⁻¹)=1
    rw [map_mul,map_inv,hq,mul_inv_cancel]
  have he := F.affineTranslation_kernel_mul k v
  have hkv : (k:U)*v=u := by dsimp [k]; group
  rw [hkv] at he
  have hd : F.affineTranslation u-F.affineTranslation v=F.bits k := by
    rw [he,add_sub_cancel_right]
  refine ⟨(F.kernelSpaceHom k).toAdd,?_,?_⟩
  · exact ⟨Additive.ofMul (⟨k,hkN⟩:N.subgroupOf F.top.ker),rfl⟩
  · exact hd.symm

/-- Centrality in the original quotient gives the exact difference of
the two affine products, in the original lower module. The top-commuting
condition is explicit when the whole normal subgroup may have nontrivial
top image. -/
theorem affine_commutator_mem_normalSpace (u v : U)
    (hu : QuotientGroup.mk' N u∈Subgroup.center (U ⧸ N))
    (ht : F.top (u*v)=F.top (v*u)) :
    (permutationFunctionRepresentation (ZMod 2) F.top.range I
      (F.top.rangeRestrict u) (F.affineTranslation v)+F.affineTranslation u)-
    (permutationFunctionRepresentation (ZMod 2) F.top.range I
      (F.top.rangeRestrict v) (F.affineTranslation u)+F.affineTranslation v)∈
      (F.normalSpace N).map F.kernelSpace.subtype := by
  have hq : QuotientGroup.mk' N (u*v)=QuotientGroup.mk' N (v*u) := by
    simpa only [map_mul] using
      (Subgroup.mem_center_iff.mp hu (QuotientGroup.mk' N v)).symm
  have h := F.affineTranslation_sub_mem_normalSpace N (u*v) (v*u) ht hq
  simpa only [F.affineTranslation_mul] using h

/-- For an actual denominator inside the pair kernel, centrality itself
forces the top images to commute. This is the version applied to the
literal intersection K∩N; it does not assert that the whole N lies in K. -/
theorem affine_commutator_mem_normalSpace_of_le_kernel
    (hN : N≤F.top.ker) (u v : U)
    (hu : QuotientGroup.mk' N u∈Subgroup.center (U ⧸ N)) :
    (permutationFunctionRepresentation (ZMod 2) F.top.range I
      (F.top.rangeRestrict u) (F.affineTranslation v)+F.affineTranslation u)-
    (permutationFunctionRepresentation (ZMod 2) F.top.range I
      (F.top.rangeRestrict v) (F.affineTranslation u)+F.affineTranslation v)∈
      (F.normalSpace N).map F.kernelSpace.subtype := by
  apply F.affine_commutator_mem_normalSpace N u v hu
  have hq : QuotientGroup.mk' N (u*v)=QuotientGroup.mk' N (v*u) := by
    simpa only [map_mul] using
      (Subgroup.mem_center_iff.mp hu (QuotientGroup.mk' N v)).symm
  exact congrArg (QuotientGroup.lift N F.top hN) hq

end SymmetricSubgroupAsymptotics.BinaryPairFrame
