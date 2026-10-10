import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopTowerOuterNestedQuotient

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

/-! ## The three literal axes of the fixed lift -/

/-- The second-kernel coordinate state contributed by the fixed omega
lift.  This is `K` in the coupled three-head inequality. -/
def fixedOmegaInnerNaturalAxis
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    Subrepresentation
      (permutationFunctionRepresentation (ZMod 2) D.top (Fin t)) :=
  R.secondFrame.sharedOriginalAxis
    (permutationFunctionRepresentation (ZMod 2) D.top (Fin t))
    R.topEquiv R.module_action_eq
    ((R.rawKernelOmegaFixedOriginalPreimage N).map
      R.frame.top.rangeRestrict)

/-- The first-kernel coordinate state contributed by the fixed omega lift,
before separating its pair-sum and pair-constant coordinates. -/
def fixedOmegaOuterAxis
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    Subrepresentation
      (permutationFunctionRepresentation (ZMod 2)
        R.frame.top.range (Fin s)) :=
  R.frame.sharedOriginalAxis
    (permutationFunctionRepresentation (ZMod 2)
      R.frame.top.range (Fin s))
    (MulEquiv.refl R.frame.top.range) (fun _ _ ↦ rfl)
    (R.rawKernelOmegaFixedOriginalPreimage N)

/-- Pair-sum image `W` of the fixed first-kernel state. -/
def fixedOmegaPairSumPullbackAxis
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    Subrepresentation R.secondFrame.pulledBackCoordinateTopAction :=
  intertwinerImage
    (permutationFunctionRepresentation (ZMod 2)
      R.frame.top.range (Fin s))
    R.secondFrame.pulledBackCoordinateTopAction
    R.secondFrame.pairSumIntertwiner (R.fixedOmegaOuterAxis N)

/-- Pair-constant preimage `L` of the fixed first-kernel state. -/
def fixedOmegaConstantPullbackAxis
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    Subrepresentation R.secondFrame.pulledBackCoordinateTopAction :=
  intertwinerPreimage
    R.secondFrame.pulledBackCoordinateTopAction
    (permutationFunctionRepresentation (ZMod 2)
      R.frame.top.range (Fin s))
    R.secondFrame.pairConstantIntertwiner (R.fixedOmegaOuterAxis N)

/-- Transport the fixed pair-sum state to the literal bottom top. -/
def fixedOmegaPairSumAxis
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    Subrepresentation
      (permutationFunctionRepresentation (ZMod 2) D.top (Fin t)) :=
  R.transportInnerNaturalAxis
    (R.secondFrame.descendPulledBackSubrepresentation
      (R.fixedOmegaPairSumPullbackAxis N))

/-- Transport the fixed pair-constant state to the literal bottom top. -/
def fixedOmegaConstantAxis
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    Subrepresentation
      (permutationFunctionRepresentation (ZMod 2) D.top (Fin t)) :=
  R.transportInnerNaturalAxis
    (R.secondFrame.descendPulledBackSubrepresentation
      (R.fixedOmegaConstantPullbackAxis N))

theorem fixedOmegaInnerNaturalAxis_toSubmodule
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    (R.fixedOmegaInnerNaturalAxis N).toSubmodule =
      R.secondFrame.ambientAxis
        ((R.rawKernelOmegaFixedOriginalPreimage N).map
          R.frame.top.rangeRestrict) :=
  rfl

theorem fixedOmegaPairSumAxis_toSubmodule
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    (R.fixedOmegaPairSumAxis N).toSubmodule =
      (R.frame.ambientAxis
          (R.rawKernelOmegaFixedOriginalPreimage N)).map
        R.secondFrame.pairSum :=
  rfl

theorem fixedOmegaConstantAxis_toSubmodule
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    (R.fixedOmegaConstantAxis N).toSubmodule =
      (R.frame.ambientAxis
          (R.rawKernelOmegaFixedOriginalPreimage N)).comap
        R.secondFrame.pairConstant :=
  rfl

/-- The fixed-lift product lies in the literal original-normal constant
denominator.  This is the formal `[B,D] = KW ≤ L ∩ N` step. -/
theorem fixedOmega_productSpan_le_normalConstant
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    binaryCoordinateProductSpan
        (R.fixedOmegaInnerNaturalAxis N).toSubmodule
        (R.fixedOmegaPairSumAxis N).toSubmodule ≤
      (R.outerNormalConstantAxis N).toSubmodule := by
  rw [R.fixedOmegaInnerNaturalAxis_toSubmodule N,
    R.fixedOmegaPairSumAxis_toSubmodule N]
  change binaryCoordinateProductSpan
      (R.secondFrame.ambientAxis
        ((R.rawKernelOmegaFixedOriginalPreimage N).map
          R.frame.top.rangeRestrict))
      ((R.frame.ambientAxis
        (R.rawKernelOmegaFixedOriginalPreimage N)).map
          R.secondFrame.pairSum) ≤
    (R.frame.ambientAxis N.1).comap R.secondFrame.pairConstant
  exact R.frame.nestedPair_productSpan_le_normalConstantPreimage
    R.secondFrame N.1 (R.rawKernelOmegaFixedOriginalPreimage N)
    (R.originalNormal_le_rawKernelOmegaFixedOriginalPreimage N)
    (by
      intro u hu k hk
      exact R.rawKernelOmegaFixedOriginalPreimage_commutator_mem
        N k.1 u hk hu)

theorem outerNormalConstant_le_fixedOmegaConstant
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    R.outerNormalConstantAxis N ≤ R.fixedOmegaConstantAxis N := by
  intro v hv
  change v ∈
    (R.frame.ambientAxis
      (R.rawKernelOmegaFixedOriginalPreimage N)).comap
        R.secondFrame.pairConstant
  change R.secondFrame.pairConstant v ∈ R.frame.ambientAxis N.1 at hv
  obtain ⟨k, hk, hkv⟩ := (R.frame.mem_ambientAxis N.1 _).1 hv
  exact (R.frame.mem_ambientAxis _ _).2
    ⟨k, R.originalNormal_le_rawKernelOmegaFixedOriginalPreimage N hk, hkv⟩

theorem fixedOmega_productSpan_le_constant
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    binaryCoordinateProductSpan
        (R.fixedOmegaInnerNaturalAxis N).toSubmodule
        (R.fixedOmegaPairSumAxis N).toSubmodule ≤
      (R.fixedOmegaConstantAxis N).toSubmodule :=
  (R.fixedOmega_productSpan_le_normalConstant N).trans
    (R.outerNormalConstant_le_fixedOmegaConstant N)

end DegreeTwoPairTopTowerRealization
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
