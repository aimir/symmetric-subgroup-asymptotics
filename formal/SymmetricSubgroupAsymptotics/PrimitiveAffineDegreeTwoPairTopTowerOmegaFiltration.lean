import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopTowerQuotient
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoRelativeKernelOrbitAnchor
import SymmetricSubgroupAsymptotics.RepresentationFixedExact
import SymmetricSubgroupAsymptotics.SchurTargetExtension

/-!
# The omega filtration through two pair kernels

The central omega of the direct two-frame kernel maps onto its actual image
in the second section module.  This file records that map equivariantly for
the original quotient action, retaining the literal kernels and charts.
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

/-- Projection to the second kernel commutes with ambient conjugation on
the intrinsic central omega. -/
theorem rawKernelOmegaProjection_conjugate
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal})
    (q : preE7PairAction s p ⧸ N.1)
    (z : binaryCentralOmega (R.rawQuotientMap N).ker) :
    R.rawKernelOmegaProjection N
        (binaryKernelOmegaConjugateOmega (R.rawQuotientMap N) q z) =
      MulAut.conjNormal (R.outerQuotientMap N q)
        (R.rawKernelOmegaProjection N z) := by
  apply Subtype.ext
  change R.outerQuotientMap N
      ((binaryKernelOmegaConjugate
        (R.rawQuotientMap N) q z : (R.rawQuotientMap N).ker) :
          preE7PairAction s p ⧸ N.1) =
    R.outerQuotientMap N q *
      (R.rawKernelOmegaProjection N z :
        R.frame.top.range ⧸ R.outerTopNormal N.1) *
      (R.outerQuotientMap N q)⁻¹
  rw [binaryKernelOmegaConjugate_val, map_mul, map_mul, map_inv]
  rfl

/-- The projected omega coordinate map is equivariant for the original
quotient, with the second section action pulled back along the direct map. -/
theorem rawKernelOmegaInnerSectionMap_equivariant
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal})
    (q : preE7PairAction s p ⧸ N.1)
    (z : binaryCentralOmega (R.rawQuotientMap N).ker) :
    R.rawKernelOmegaInnerSectionMap N
        (binaryKernelOmegaConjugationRepresentation
          (R.rawQuotientMap N) q (Additive.ofMul z)) =
      (R.innerSectionModule N).ρ (R.rawQuotientMap N q)
        (R.rawKernelOmegaInnerSectionMap N (Additive.ofMul z)) := by
  let E := R.innerSectionModuleChart N
  change (E.equiv.symm
      (R.rawKernelOmegaProjection N
        (binaryKernelOmegaConjugateOmega
          (R.rawQuotientMap N) q z))).toAdd =
    (R.innerSectionModule N).ρ
      (R.innerQuotientMap N (R.outerQuotientMap N q))
      (E.equiv.symm (R.rawKernelOmegaProjection N z)).toAdd
  apply Multiplicative.ofAdd.injective
  apply E.equiv.injective
  apply Subtype.ext
  rw [E.equiv.apply_symm_apply]
  rw [E.conjugate]
  exact congrArg Subtype.val
    (R.rawKernelOmegaProjection_conjugate N q z)

/-- The concrete omega-to-inner-section map as an intertwiner of original
quotient representations. -/
noncomputable def rawKernelOmegaInnerSectionIntertwiner
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    (binaryKernelOmegaConjugationRepresentation
      (R.rawQuotientMap N)).IntertwiningMap
      ((R.innerSectionModule N).ρ.comp (R.rawQuotientMap N)) where
  toLinearMap := R.rawKernelOmegaInnerSectionMap N
  isIntertwining' := by
    intro q
    apply LinearMap.ext
    intro z
    obtain ⟨z, rfl⟩ := Additive.toMul.surjective z
    exact R.rawKernelOmegaInnerSectionMap_equivariant N q z

/-- Corestrict the omega projection to its exact inner image. -/
noncomputable def rawKernelOmegaInnerImageIntertwiner
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    (binaryKernelOmegaConjugationRepresentation
      (R.rawQuotientMap N)).IntertwiningMap
      ((R.innerOmegaSubrepresentation N).toRepresentation.comp
        (R.rawQuotientMap N)) where
  toLinearMap := (R.rawKernelOmegaInnerSectionMap N).codRestrict
    (R.innerOmegaSubrepresentation N).toSubmodule (fun z ↦ by
      rw [← R.rawKernelOmegaInnerSectionMap_range_eq N]
      exact ⟨z, rfl⟩)
  isIntertwining' := by
    intro q
    apply LinearMap.ext
    intro z
    apply Subtype.ext
    exact Representation.IntertwiningMap.isIntertwining _ _
      (R.rawKernelOmegaInnerSectionIntertwiner N) q z

theorem rawKernelOmegaInnerImageIntertwiner_surjective
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    Function.Surjective (R.rawKernelOmegaInnerImageIntertwiner N) := by
  rintro ⟨v, hv⟩
  have hvrange : v ∈
      LinearMap.range (R.rawKernelOmegaInnerSectionMap N) := by
    rw [R.rawKernelOmegaInnerSectionMap_range_eq N]
    exact hv
  obtain ⟨z, hz⟩ := hvrange
  exact ⟨z, Subtype.ext hz⟩

/-- The linear kernel of the inner-image intertwiner is the additive form of
the literal group kernel of omega projection. -/
noncomputable def rawKernelOmegaInnerKernelEquivProjectionKernel
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    (R.rawKernelOmegaInnerImageIntertwiner N).ker.toSubmodule ≃ₗ[ZMod 2]
      Additive (R.rawKernelOmegaProjection N).ker := by
  let f : (R.rawKernelOmegaInnerImageIntertwiner N).ker.toSubmodule →ₗ[ZMod 2]
      Additive (R.rawKernelOmegaProjection N).ker where
    toFun := fun z ↦ Additive.ofMul ⟨z.1.toMul, by
      apply MonoidHom.mem_ker.mpr
      let E := R.innerSectionModuleChart N
      have hz : R.rawKernelOmegaInnerSectionMap N z.1 = 0 :=
        congrArg Subtype.val z.2
      apply E.equiv.symm.injective
      change Multiplicative.ofAdd
          (R.rawKernelOmegaInnerSectionMap N z.1) = _
      rw [hz]
      rfl⟩
    map_add' _ _ := rfl
    map_smul' _ _ := rfl
  apply LinearEquiv.ofBijective f
  constructor
  · intro z w hzw
    apply Subtype.ext
    exact Additive.toMul.injective
      (congrArg (fun a : Additive (R.rawKernelOmegaProjection N).ker ↦
        a.toMul.1) hzw)
  · intro z
    let x : Additive
        (binaryCentralOmega (R.rawQuotientMap N).ker) :=
      Additive.ofMul z.toMul.1
    have hx : x ∈ (R.rawKernelOmegaInnerImageIntertwiner N).ker := by
      apply Subtype.ext
      change R.rawKernelOmegaInnerSectionMap N x = 0
      rw [R.rawKernelOmegaInnerSectionMap_apply N z.toMul.1]
      rw [MonoidHom.mem_ker.mp z.toMul.2]
      change ((R.innerSectionModuleChart N).equiv.symm 1).toAdd = 0
      rw [map_one]
      rfl
    exact ⟨⟨x, hx⟩, rfl⟩

/-- Applying the first zero-cut chart to an outer omega coordinate recovers
the same element of the original quotient as the intrinsic omega
embedding. -/
theorem rawKernelOmegaOuterCoordinateMap_chart_val
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal})
    (z : (R.rawKernelOmegaProjection N).ker) :
    (((R.frame.zeroCutModuleChart N.1).equiv
        (Multiplicative.ofAdd
          (R.rawKernelOmegaOuterCoordinateMap N (Additive.ofMul z))) :
          (R.frame.zeroCutBase N.1).ker) :
        preE7PairAction s p ⧸ N.1) =
      ((binaryCentralOmegaEmbedding z.1 :
          (R.rawQuotientMap N).ker) :
        preE7PairAction s p ⧸ N.1) := by
  let E := R.outerZeroCutKernelEquivRawKernelProjectionKer N
  have hE : E (Multiplicative.ofAdd
      (R.rawKernelOmegaOuterCoordinateMap N (Additive.ofMul z))) =
        R.rawKernelOmegaOuterInclusion N z := by
    change E (E.symm (R.rawKernelOmegaOuterInclusion N z)) = _
    exact E.apply_symm_apply _
  exact congrArg
    (fun y : (R.rawKernelProjection N).ker ↦
      (((y : (R.rawQuotientMap N).ker) :
        preE7PairAction s p ⧸ N.1))) hE

/-- The outer coordinate map is equivariant for the original quotient
action and the first zero-cut action. -/
theorem rawKernelOmegaOuterCoordinateMap_equivariant
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal})
    (q : preE7PairAction s p ⧸ N.1)
    (z : (R.rawKernelOmegaProjection N).ker) :
    R.rawKernelOmegaOuterCoordinateMap N
        (Additive.ofMul
          ⟨binaryKernelOmegaConjugateOmega
              (R.rawQuotientMap N) q z.1,
            by
              apply MonoidHom.mem_ker.mpr
              apply Subtype.ext
              change R.outerQuotientMap N q *
                  (R.rawKernelOmegaProjection N z.1 :
                    R.frame.top.range ⧸ R.outerTopNormal N.1) *
                    (R.outerQuotientMap N q)⁻¹ = 1
              rw [MonoidHom.mem_ker.mp z.2]
              group⟩) =
      (R.frame.zeroCutModule N.1).ρ (R.frame.zeroCutBase N.1 q)
        (R.rawKernelOmegaOuterCoordinateMap N (Additive.ofMul z)) := by
  apply Multiplicative.ofAdd.injective
  apply (R.frame.zeroCutModuleChart N.1).equiv.injective
  apply Subtype.ext
  rw [(R.frame.zeroCutModuleChart N.1).conjugate]
  rw [R.rawKernelOmegaOuterCoordinateMap_chart_val N]
  rw [R.rawKernelOmegaOuterCoordinateMap_chart_val N]
  change q *
      ((binaryCentralOmegaEmbedding z.1 :
        (R.rawQuotientMap N).ker) : preE7PairAction s p ⧸ N.1) * q⁻¹ = _
  rw [binaryKernelOmegaConjugate_val]

/-- Concrete injection of the actual outer projection kernel into the first
zero-cut representation. -/
noncomputable def rawKernelOmegaOuterIntertwiner
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    (R.rawKernelOmegaInnerImageIntertwiner N).ker.toRepresentation.
      IntertwiningMap
      ((R.frame.zeroCutModule N.1).ρ.comp (R.frame.zeroCutBase N.1)) where
  toLinearMap := (R.rawKernelOmegaOuterCoordinateMap N).comp
    (R.rawKernelOmegaInnerKernelEquivProjectionKernel N).toLinearMap
  isIntertwining' := by
    intro q
    apply LinearMap.ext
    intro z
    exact R.rawKernelOmegaOuterCoordinateMap_equivariant N q
      ((R.rawKernelOmegaInnerKernelEquivProjectionKernel N) z).toMul

theorem rawKernelOmegaOuterIntertwiner_injective
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    Function.Injective (R.rawKernelOmegaOuterIntertwiner N) :=
  (R.rawKernelOmegaOuterCoordinateMap_injective N).comp
    (R.rawKernelOmegaInnerKernelEquivProjectionKernel N).injective

/-- Fixed vectors in direct-kernel omega are bounded by the two literal
terms of the projection filtration: its actual kernel and its exact inner
image. -/
theorem rawKernelOmega_invariants_finrank_le_kernel_add_inner
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    Module.finrank (ZMod 2)
        (binaryKernelOmegaConjugationRepresentation
          (R.rawQuotientMap N)).invariants ≤
      Module.finrank (ZMod 2)
          (R.rawKernelOmegaInnerImageIntertwiner N).ker.toRepresentation.invariants +
        Module.finrank (ZMod 2)
          ((R.innerOmegaSubrepresentation N).toRepresentation.comp
            (R.rawQuotientMap N)).invariants := by
  let q := R.rawKernelOmegaInnerImageIntertwiner N
  let i : q.ker.toRepresentation.IntertwiningMap
      (binaryKernelOmegaConjugationRepresentation
        (R.rawQuotientMap N)) where
    toLinearMap := q.ker.toSubmodule.subtype
    isIntertwining' := by intro _; rfl
  have hi : Function.Injective i := Subtype.val_injective
  have hexact : i.toLinearMap.range = q.toLinearMap.ker := by
    ext z
    constructor
    · rintro ⟨w, rfl⟩
      exact w.property
    · intro hz
      exact ⟨⟨z, hz⟩, rfl⟩
  exact RepresentationFixedExact.finrank_invariants_le_of_range_eq_ker
    i q hi hexact

/-- Pair-constant coordinates include the actual constant preimage `L`
into the retained first-kernel omega axis. -/
noncomputable def outerOmegaConstantInclusion
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    (R.outerOmegaConstantPullbackAxis N).toRepresentation.IntertwiningMap
      (R.outerOmegaAxis N).toRepresentation where
  toLinearMap :=
    { toFun := fun a ↦ ⟨R.secondFrame.pairConstant a.1, a.2⟩
      map_add' := by intro a b; exact Subtype.ext (map_add _ _ _)
      map_smul' := by intro c a; exact Subtype.ext (map_smul _ _ _) }
  isIntertwining' := by
    intro g
    apply LinearMap.ext
    intro a
    apply Subtype.ext
    exact Representation.IntertwiningMap.isIntertwining _ _
      R.secondFrame.pairConstantIntertwiner g a.1

theorem outerOmegaConstantInclusion_injective
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    Function.Injective (R.outerOmegaConstantInclusion N) := by
  intro a b hab
  apply Subtype.ext
  exact R.secondFrame.pairConstantIntertwiner_injective
    (congrArg Subtype.val hab)

/-- Pair-sum maps the retained outer omega axis onto its exact image `W`. -/
noncomputable def outerOmegaPairSumProjection
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    (R.outerOmegaAxis N).toRepresentation.IntertwiningMap
      (R.outerOmegaPairSumPullbackAxis N).toRepresentation where
  toLinearMap :=
    { toFun := fun b ↦
        ⟨R.secondFrame.pairSum b.1, ⟨b.1, b.2, rfl⟩⟩
      map_add' := by intro a b; exact Subtype.ext (map_add _ _ _)
      map_smul' := by intro c a; exact Subtype.ext (map_smul _ _ _) }
  isIntertwining' := by
    intro g
    apply LinearMap.ext
    intro b
    apply Subtype.ext
    exact Representation.IntertwiningMap.isIntertwining _ _
      R.secondFrame.pairSumIntertwiner g b.1

theorem outerOmegaPairSumProjection_surjective
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    Function.Surjective (R.outerOmegaPairSumProjection N) := by
  rintro ⟨w, ⟨b, hb, hbw⟩⟩
  refine ⟨⟨b, hb⟩, ?_⟩
  exact Subtype.ext hbw

/-- The pair-constant inclusion and pair-sum projection remain exact after
restriction to the actual retained omega axis. -/
theorem outerOmega_constant_pairSum_exact
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    (R.outerOmegaConstantInclusion N).toLinearMap.range =
      (R.outerOmegaPairSumProjection N).toLinearMap.ker := by
  ext b
  constructor
  · rintro ⟨a, rfl⟩
    apply Subtype.ext
    exact R.secondFrame.pairSum_pairConstant a.1
  · intro hb
    have hsum : R.secondFrame.pairSum b.1 = 0 :=
      congrArg Subtype.val hb
    have hdelta : b.1 ∈ R.secondFrame.pairDelta.ker := by
      change R.secondFrame.pairConstant
        (R.secondFrame.pairSum b.1) = 0
      rw [hsum, map_zero]
    rw [R.secondFrame.pairDelta_ker] at hdelta
    obtain ⟨a, ha⟩ := hdelta
    let aL : (R.outerOmegaConstantPullbackAxis N).toSubmodule :=
      ⟨a, by
        change R.secondFrame.pairConstant a ∈
          (R.outerOmegaAxis N).toSubmodule
        rw [ha]
        exact b.2⟩
    refine ⟨aL, ?_⟩
    exact Subtype.ext ha

/-- Fixed-space subadditivity on the literal outer `L-B-W` sequence. -/
theorem outerOmega_invariants_finrank_le_constant_add_pairSum
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    Module.finrank (ZMod 2)
        (R.outerOmegaAxis N).toRepresentation.invariants ≤
      Module.finrank (ZMod 2)
          (R.outerOmegaConstantPullbackAxis N).toRepresentation.invariants +
        Module.finrank (ZMod 2)
          (R.outerOmegaPairSumPullbackAxis N).toRepresentation.invariants :=
  RepresentationFixedExact.finrank_invariants_le_of_range_eq_ker
    (R.outerOmegaConstantInclusion N)
    (R.outerOmegaPairSumProjection N)
    (R.outerOmegaConstantInclusion_injective N)
    (R.outerOmega_constant_pairSum_exact N)

end DegreeTwoPairTopTowerRealization
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
