import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopTowerOmegaFiltration

/-!
# The fixed direct-omega lift in a two-frame pair tower

The coupled trivial-row argument must lift the fixed part of the direct
kernel omega, rather than the whole omega module.  In the original quotient
this lift is intrinsic: it is the intersection of the ambient omega subgroup
with the center.  This file identifies that literal subgroup with the fixed
space of the omega conjugation representation and pulls it back to the
original pair action.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoPairTopTowerRealization

variable {s t : ℕ} {D : DegreeTwoPairTopFiniteInterface t}
  {p : PreE7PairActionClass s}
  (R : DegreeTwoPairTopTowerRealization D p)

/-- The actual central part of the direct-kernel omega subgroup in the
original quotient. -/
def rawKernelOmegaFixedLift
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    Subgroup (preE7PairAction s p ⨸ N.1) :=
  R.rawKernelOmegaLift N ⊓ Subgroup.center (preE7PairAction s p ⨸ N.1)

instance rawKernelOmegaFixedLift_normal
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    (R.rawKernelOmegaFixedLift N).Normal :=
  inferInstance

/-- Pull the fixed omega lift back to the original action.  This is the
normal subgroup denoted `D` in the three-layer coupled-head argument. -/
def rawKernelOmegaFixedOriginalPreimage
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    Subgroup (preE7PairAction s p) := by
  letI : N.1.Normal := N.2
  exact (R.rawKernelOmegaFixedLift N).comap (QuotientGroup.mk' N.1)

instance rawKernelOmegaFixedOriginalPreimage_normal
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    (R.rawKernelOmegaFixedOriginalPreimage N).Normal := by
  letI : N.1.Normal := N.2
  exact Subgroup.Normal.comap inferInstance (QuotientGroup.mk' N.1)

theorem originalNormal_le_rawKernelOmegaFixedOriginalPreimage
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    N.1 ≤ R.rawKernelOmegaFixedOriginalPreimage N := by
  intro u hu
  change QuotientGroup.mk' N.1 u ∈ R.rawKernelOmegaFixedLift N
  rw [QuotientGroup.eq_one_iff.mpr hu]
  exact Subgroup.one_mem _

/-- A fixed omega vector gives a central element of the original quotient.
The statement keeps the concrete omega embedding visible for later
coordinate calculations. -/
theorem binaryCentralOmegaEmbedding_mem_center_of_fixed
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal})
    (z : binaryCentralOmega (R.rawQuotientMap N).ker)
    (hz : Additive.ofMul z ∈
      (binaryKernelOmegaConjugationRepresentation
        (R.rawQuotientMap N)).invariants) :
    (binaryCentralOmegaEmbedding z : preE7PairAction s p ⨸ N.1) ∈
      Subgroup.center (preE7PairAction s p ⨸ N.1) := by
  apply Subgroup.mem_center_iff.mpr
  intro q
  have hfix := hz q
  change Additive.ofMul
      (binaryKernelOmegaConjugateOmega (R.rawQuotientMap N) q z) =
        Additive.ofMul z at hfix
  have hconj := congrArg
    (fun w : Additive (binaryCentralOmega (R.rawQuotientMap N).ker) ↦
      (binaryCentralOmegaEmbedding w.toMul :
        preE7PairAction s p ⨸ N.1)) hfix
  rw [binaryKernelOmegaConjugate_val] at hconj
  have hright := congrArg
    (fun x : preE7PairAction s p ⨸ N.1 ↦ x * q) hconj
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using hright

/-- Conversely, an omega element central in the original quotient is fixed
by the whole omega conjugation representation. -/
theorem fixed_of_binaryCentralOmegaEmbedding_mem_center
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal})
    (z : binaryCentralOmega (R.rawQuotientMap N).ker)
    (hz : (binaryCentralOmegaEmbedding z : preE7PairAction s p ⨸ N.1) ∈
      Subgroup.center (preE7PairAction s p ⨸ N.1)) :
    Additive.ofMul z ∈
      (binaryKernelOmegaConjugationRepresentation
        (R.rawQuotientMap N)).invariants := by
  intro q
  apply Additive.toMul.injective
  apply binaryCentralOmegaEmbedding_injective
  apply Subtype.ext
  rw [binaryKernelOmegaConjugate_val]
  have hc := Subgroup.mem_center_iff.mp hz q
  calc
    q * (binaryCentralOmegaEmbedding z :
        preE7PairAction s p ⨸ N.1) * q⁻¹ =
        (binaryCentralOmegaEmbedding z :
          preE7PairAction s p ⨸ N.1) * q * q⁻¹ := by rw [hc]
    _ = (binaryCentralOmegaEmbedding z :
          preE7PairAction s p ⨸ N.1) := by simp

/-- The underlying additive group of the fixed omega lift is elementary
binary, because it is contained in the ambient omega subgroup. -/
instance rawKernelOmegaFixedLift_module
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    Module (ZMod 2) (Additive (R.rawKernelOmegaFixedLift N)) :=
  AddCommGroup.zmodModule (n := 2) (fun x ↦ by
    apply Additive.toMul.injective
    apply Subtype.ext
    change (x.toMul.1 : preE7PairAction s p ⨸ N.1) ^ 2 = 1
    exact x.toMul.2.1.2.2.2)

/-- Fixed vectors in raw omega are exactly the additive form of the literal
central omega lift. -/
noncomputable def rawKernelOmegaInvariantsEquivFixedLift
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    (binaryKernelOmegaConjugationRepresentation
        (R.rawQuotientMap N)).invariants ≃ₗ[ZMod 2]
      Additive (R.rawKernelOmegaFixedLift N) where
  toFun v := Additive.ofMul
    ⟨(R.rawKernelOmegaEquiv N v.1.toMul :
        R.rawKernelOmegaLift N).1,
      (R.rawKernelOmegaEquiv N v.1.toMul).2,
      by
        rw [R.rawKernelOmegaEquiv_val N]
        exact R.binaryCentralOmegaEmbedding_mem_center_of_fixed
          N v.1.toMul v.2⟩
  invFun z :=
    let omega := (R.rawKernelOmegaEquiv N).symm
      ⟨z.toMul.1, z.toMul.2.1⟩
    ⟨Additive.ofMul omega, by
      apply R.fixed_of_binaryCentralOmegaEmbedding_mem_center N omega
      rw [← R.rawKernelOmegaEquiv_val N omega]
      have he := congrArg Subtype.val
        ((R.rawKernelOmegaEquiv N).apply_symm_apply
          ⟨z.toMul.1, z.toMul.2.1⟩)
      exact he.symm ▸ z.toMul.2.2⟩
  left_inv v := by
    apply Subtype.ext
    apply Additive.toMul.injective
    exact (R.rawKernelOmegaEquiv N).symm_apply_apply v.1.toMul
  right_inv z := by
    apply Additive.toMul.injective
    apply Subtype.ext
    exact congrArg Subtype.val
      ((R.rawKernelOmegaEquiv N).apply_symm_apply
        ⟨z.toMul.1, z.toMul.2.1⟩)
  map_add' v w := by
    apply Additive.toMul.injective
    apply Subtype.ext
    exact congrArg Subtype.val
      (map_mul (R.rawKernelOmegaEquiv N) v.1.toMul w.1.toMul)
  map_smul' c v := by
    fin_cases c <;>
      simp only [zero_smul, one_smul, map_zero, map_one]

theorem rawKernelOmegaFixedOriginalPreimage_commutator_mem
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal})
    (u v : preE7PairAction s p)
    (hu : u ∈ R.rawKernelOmegaFixedOriginalPreimage N)
    (hv : v ∈ R.rawKernelOmegaFixedOriginalPreimage N) :
    u⁻¹ * v * u * v⁻¹ ∈ N.1 := by
  letI : N.1.Normal := N.2
  apply (QuotientGroup.eq_one_iff _).mp
  simp only [map_mul, map_inv]
  have hcentral : Commute (QuotientGroup.mk' N.1 u)
      (QuotientGroup.mk' N.1 v) :=
    (Subgroup.mem_center_iff.mp hv.2.2
      (QuotientGroup.mk' N.1 u)).symm
  rw [hcentral.eq]
  group

end DegreeTwoPairTopTowerRealization
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
