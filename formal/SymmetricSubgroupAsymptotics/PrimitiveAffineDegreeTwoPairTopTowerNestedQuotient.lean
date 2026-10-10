import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopTowerQuotient
import SymmetricSubgroupAsymptotics.BinaryPairRankThreeResidual

/-!
# The inner omega layer as a nested natural-module quotient

The second-frame image of direct-kernel omega is obtained by quotienting its
natural coordinate axis by the coordinate axis of the original normal
subgroup.  This file identifies that literal quotient with the exact image
of the corresponding state in the actual pair section.  It also transports
the action from the selected catalogue top to the physical second-frame top.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoPairTopTowerRealization

variable {s t : ℕ} {D : DegreeTwoPairTopFiniteInterface t}
  {p : PreE7PairActionClass s}
  (R : DegreeTwoPairTopTowerRealization D p)

/-- The original-normal coordinate axis is contained in the inner omega
coordinate axis. -/
theorem moduleAxis_le_innerOmegaNaturalAxis
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    R.moduleAxis N ≤ R.innerOmegaNaturalAxis N := by
  intro v hv
  change v ∈ R.secondFrame.ambientAxis
    (R.rawKernelOmegaIntermediatePreimage N)
  change v ∈ R.secondFrame.ambientAxis (R.outerTopNormal N.1) at hv
  obtain ⟨k, hk, rfl⟩ := (R.secondFrame.mem_ambientAxis _ v).1 hv
  exact (R.secondFrame.mem_ambientAxis _ _).2
    ⟨k, R.outerTopNormal_le_rawKernelOmegaIntermediatePreimage N hk, rfl⟩

/-- Pulling the literal nested quotient back along the top equivalence gives
the identical quotient formed in physical second-frame coordinates. -/
def innerNestedQuotientCoordinateEquiv
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    ((nestedQuotientRepresentation
      (R.moduleAxis N) (R.innerOmegaNaturalAxis N)
      (R.moduleAxis_le_innerOmegaNaturalAxis N)).comp
        R.topEquiv.symm.toMonoidHom).Equiv
      (nestedQuotientRepresentation
        (R.innerNormalCoordinateAxis N) (R.innerOmegaCoordinateAxis N)
        (R.innerNormalCoordinateAxis_le_innerOmegaCoordinateAxis N)) :=
  Representation.Equiv.mk (LinearEquiv.refl _ _) (by
    intro g
    apply LinearMap.ext
    intro x
    obtain ⟨b, rfl⟩ :=
      (nestedSubrepresentation
        (R.moduleAxis N) (R.innerOmegaNaturalAxis N)
        (R.moduleAxis_le_innerOmegaNaturalAxis N)).toSubmodule.
          mkQ_surjective x
    apply congrArg
      (nestedSubrepresentation
        (R.innerNormalCoordinateAxis N) (R.innerOmegaCoordinateAxis N)
        (R.innerNormalCoordinateAxis_le_innerOmegaCoordinateAxis N)).toSubmodule.mkQ
    apply Subtype.ext
    rw [R.module_action_eq, R.topEquiv.apply_symm_apply])

/-- The transported natural quotient is the exact image of the omega state
under the actual second-frame section map. -/
noncomputable def innerNestedQuotientSectionImageEquiv
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    ((nestedQuotientRepresentation
      (R.moduleAxis N) (R.innerOmegaNaturalAxis N)
      (R.moduleAxis_le_innerOmegaNaturalAxis N)).comp
        R.topEquiv.symm.toMonoidHom).Equiv
      (intertwinerImage
        R.secondFrame.kernelTopPermutationSubrepresentation.toRepresentation
        (R.secondFrame.sectionTopRepresentation (R.outerTopNormal N.1))
        (R.secondFrame.sectionTopIntertwiner (R.outerTopNormal N.1))
        (nestedSubrepresentation (R.innerOmegaCoordinateAxis N)
          R.secondFrame.kernelTopPermutationSubrepresentation
          (R.innerOmegaCoordinateAxis_le_kernelTop N))).toRepresentation := by
  let hAB : R.secondFrame.normalTopPermutationSubrepresentation
      (R.outerTopNormal N.1) ≤ R.innerOmegaCoordinateAxis N := by
    rw [← R.innerNormalCoordinateAxis_eq_normalTopPermutation N]
    exact R.innerNormalCoordinateAxis_le_innerOmegaCoordinateAxis N
  let eImage := R.secondFrame.sectionTopNestedQuotientImageEquiv
    (R.outerTopNormal N.1) (R.innerOmegaCoordinateAxis N) hAB
      (R.innerOmegaCoordinateAxis_le_kernelTop N)
  rw [← R.innerNormalCoordinateAxis_eq_normalTopPermutation N] at eImage
  exact (R.innerNestedQuotientCoordinateEquiv N).trans eImage

/-- The exact section-map image in the preceding equivalence is the inner
omega subrepresentation already constructed from the physical subgroup
image. -/
theorem innerSectionImage_toSubmodule_eq_innerOmega
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    (intertwinerImage
      R.secondFrame.kernelTopPermutationSubrepresentation.toRepresentation
      (R.secondFrame.sectionTopRepresentation (R.outerTopNormal N.1))
      (R.secondFrame.sectionTopIntertwiner (R.outerTopNormal N.1))
      (nestedSubrepresentation (R.innerOmegaCoordinateAxis N)
        R.secondFrame.kernelTopPermutationSubrepresentation
        (R.innerOmegaCoordinateAxis_le_kernelTop N))).toSubmodule =
      (R.innerOmegaSubrepresentation N).toSubmodule := by
  letI : (R.outerTopNormal N.1).Normal := R.outerTopNormal_normal N.1
  let E := R.innerSectionModuleChart N
  let L := (R.rawKernelOmegaTopImage N).subgroupOf
    (R.innerQuotientMap N).ker
  have hker : (E.kernelCoordinates
      (R.innerQuotientMap N) (R.innerSectionModule N)).ker ≤ L := by
    intro x hx
    have hx1 : x = 1 := by
      apply E.equiv.symm.injective
      exact (MonoidHom.mem_ker.mp hx).trans
        (map_one E.equiv.symm).symm
    subst x
    exact Subgroup.one_mem _
  ext v
  constructor
  · rintro ⟨b, hb, rfl⟩
    change b.1 ∈ (R.innerOmegaCoordinateAxis N).toSubmodule at hb
    change b.1 ∈ R.secondFrame.ambientAxis
      (R.rawKernelOmegaIntermediatePreimage N) at hb
    obtain ⟨k, hk, hkb⟩ :=
      (R.secondFrame.mem_ambientAxis _ b.1).1 hb
    have hbEq : (R.secondFrame.kernelSpaceHom k).toAdd = b := by
      apply Subtype.ext
      exact hkb
    rw [← hbEq]
    change ((E.kernelCoordinates
      (R.innerQuotientMap N) (R.innerSectionModule N)
      (E.equiv (Multiplicative.ofAdd
        ((R.secondFrame.normalSpace (R.outerTopNormal N.1)).mkQ
          (R.secondFrame.kernelSpaceHom k).toAdd)))).toAdd) ∈
      E.normalSpace (R.innerQuotientMap N)
        (R.innerSectionModule N) L
    apply (sectionSubgroupImage_mem_iff
      (E.kernelCoordinates (R.innerQuotientMap N)
        (R.innerSectionModule N)) L hker _).2
    change (E.equiv (Multiplicative.ofAdd
      ((R.secondFrame.normalSpace (R.outerTopNormal N.1)).mkQ
        (R.secondFrame.kernelSpaceHom k).toAdd)) :
          R.frame.top.range ⧸ R.outerTopNormal N.1) ∈
      R.rawKernelOmegaTopImage N
    have he := R.secondFrame.literalSectionModuleChart_equiv_mk
      R.topEquiv (R.outerTopNormal N.1) k
    rw [show E = R.secondFrame.literalSectionModuleChart
      R.topEquiv (R.outerTopNormal N.1) from rfl]
    rw [he]
    exact hk
  · intro hv
    change v ∈ E.normalSpace (R.innerQuotientMap N)
      (R.innerSectionModule N) L at hv
    let y : (R.innerQuotientMap N).ker :=
      E.equiv (Multiplicative.ofAdd v)
    have hcoord : (E.kernelCoordinates
        (R.innerQuotientMap N) (R.innerSectionModule N) y).toAdd = v := by
      change (E.equiv.symm (E.equiv (Multiplicative.ofAdd v))).toAdd = v
      rw [E.equiv.symm_apply_apply]
      rfl
    have hy : y ∈ L := by
      apply (sectionSubgroupImage_mem_iff
        (E.kernelCoordinates (R.innerQuotientMap N)
          (R.innerSectionModule N)) L hker y).1
      rwa [hcoord]
    obtain ⟨x, hx⟩ :=
      (R.secondFrame.normalSpace (R.outerTopNormal N.1)).mkQ_surjective v
    obtain ⟨k, hk⟩ := R.secondFrame.kernelSpaceHom_bijective.2
      (Multiplicative.ofAdd x)
    have hxk : (R.secondFrame.kernelSpaceHom k).toAdd = x :=
      congrArg Multiplicative.toAdd hk
    have hyval :
        (y : R.frame.top.range ⧸ R.outerTopNormal N.1) =
          QuotientGroup.mk' (R.outerTopNormal N.1)
            (k : R.frame.top.range) := by
      change ((E.equiv (Multiplicative.ofAdd v) :
        (R.innerQuotientMap N).ker) :
          R.frame.top.range ⧸ R.outerTopNormal N.1) = _
      rw [← hx, ← hxk]
      have he := R.secondFrame.literalSectionModuleChart_equiv_mk
        R.topEquiv (R.outerTopNormal N.1) k
      simpa only [E, innerSectionModuleChart, innerSectionModule,
        innerQuotientMap] using he
    have hkOmega : (k : R.frame.top.range) ∈
        R.rawKernelOmegaIntermediatePreimage N := by
      change QuotientGroup.mk' (R.outerTopNormal N.1)
        (k : R.frame.top.range) ∈ R.rawKernelOmegaTopImage N
      rw [← hyval]
      exact hy
    let b : R.secondFrame.kernelTopPermutationSubrepresentation.toSubmodule :=
      (R.secondFrame.kernelSpaceHom k).toAdd
    have hb : b.1 ∈ (R.innerOmegaCoordinateAxis N).toSubmodule := by
      change R.secondFrame.bits k ∈
        R.secondFrame.ambientAxis
          (R.rawKernelOmegaIntermediatePreimage N)
      exact (R.secondFrame.bits_mem_ambientAxis _ k).2 hkOmega
    refine ⟨b, hb, ?_⟩
    change (R.secondFrame.normalSpace (R.outerTopNormal N.1)).mkQ b = v
    rw [show (b : R.secondFrame.kernelSpace) = x from hxk, hx]

end DegreeTwoPairTopTowerRealization
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
