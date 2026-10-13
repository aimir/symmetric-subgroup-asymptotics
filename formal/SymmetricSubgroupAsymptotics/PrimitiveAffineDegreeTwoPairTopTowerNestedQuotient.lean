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
    Representation.Equiv ((nestedQuotientRepresentation
      (R.moduleAxis N) (R.innerOmegaNaturalAxis N)
      (R.moduleAxis_le_innerOmegaNaturalAxis N)).comp
        R.topEquiv.symm.toMonoidHom)
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
        (R.moduleAxis_le_innerOmegaNaturalAxis N)).toSubmodule.mkQ_surjective x
    apply congrArg
      (nestedSubrepresentation
        (R.innerNormalCoordinateAxis N) (R.innerOmegaCoordinateAxis N)
        (R.innerNormalCoordinateAxis_le_innerOmegaCoordinateAxis N)).toSubmodule.mkQ
    apply Subtype.ext
    change permutationFunctionRepresentation (ZMod 2) D.top (Fin t)
      (R.topEquiv.symm g) b.1 = R.secondFrame.coordinateTopAction g b.1
    rw [R.module_action_eq, R.topEquiv.apply_symm_apply])

/-- The transported natural quotient is the exact image of the omega state
under the actual second-frame section map. -/
noncomputable def innerNestedQuotientSectionImageEquiv
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    Representation.Equiv ((nestedQuotientRepresentation
      (R.moduleAxis N) (R.innerOmegaNaturalAxis N)
      (R.moduleAxis_le_innerOmegaNaturalAxis N)).comp
        R.topEquiv.symm.toMonoidHom)
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
  have transport (A A' B : Subrepresentation R.secondFrame.coordinateTopAction)
      (hAB : A ≤ B) (hA'B : A' ≤ B) (h : A = A') :
      Nonempty ((nestedQuotientRepresentation A B hAB).Equiv
        (nestedQuotientRepresentation A' B hA'B)) := by
    subst A'
    exact ⟨Representation.Equiv.refl _⟩
  let eDenominator := Classical.choice (transport
    (R.innerNormalCoordinateAxis N)
    (R.secondFrame.normalTopPermutationSubrepresentation (R.outerTopNormal N.1))
    (R.innerOmegaCoordinateAxis N)
    (R.innerNormalCoordinateAxis_le_innerOmegaCoordinateAxis N) hAB
    (R.innerNormalCoordinateAxis_eq_normalTopPermutation N))
  exact (R.innerNestedQuotientCoordinateEquiv N).trans (eDenominator.trans eImage)

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
    let v := (R.secondFrame.normalSpace (R.outerTopNormal N.1)).mkQ
      (R.secondFrame.kernelSpaceHom k).toAdd
    have hcoord : (E.kernelCoordinates
        (R.innerQuotientMap N) (R.innerSectionModule N)
        (E.equiv (Multiplicative.ofAdd v))).toAdd = v := by
      change (E.equiv.symm (E.equiv (Multiplicative.ofAdd v))).toAdd = v
      rw [E.equiv.symm_apply_apply]
      rfl
    change v ∈ E.normalSpace (R.innerQuotientMap N)
      (R.innerSectionModule N) (R.rawKernelOmegaTopImage N)
    rw [← hcoord]
    apply (sectionSubgroupImage_mem_iff (p := 2)
      (E.kernelCoordinates (R.innerQuotientMap N)
        (R.innerSectionModule N)) L hker _).2
    change (E.equiv (Multiplicative.ofAdd
      ((R.secondFrame.normalSpace (R.outerTopNormal N.1)).mkQ
        (R.secondFrame.kernelSpaceHom k).toAdd)) :
          R.frame.top.range ⧸ R.outerTopNormal N.1) ∈
      R.rawKernelOmegaTopImage N
    have he := R.secondFrame.literalSectionModuleChart_equiv_mk
      R.topEquiv (R.outerTopNormal N.1) k
    have he' : ((E.equiv (Multiplicative.ofAdd
        ((R.secondFrame.normalSpace (R.outerTopNormal N.1)).mkQ
          (R.secondFrame.kernelSpaceHom k).toAdd)) :
            (R.innerQuotientMap N).ker) :
              R.frame.top.range ⧸ R.outerTopNormal N.1) =
        QuotientGroup.mk' (R.outerTopNormal N.1) (k : R.frame.top.range) := by
      simpa only [E, innerSectionModuleChart, innerSectionModule,
        innerQuotientMap] using he
    exact (congrArg (fun q : R.frame.top.range ⧸ R.outerTopNormal N.1 ↦
      q ∈ R.rawKernelOmegaTopImage N) he').mpr hk
  · intro hv
    change v ∈ E.normalSpace (R.innerQuotientMap N)
      (R.innerSectionModule N) (R.rawKernelOmegaTopImage N) at hv
    let y : (R.innerQuotientMap N).ker :=
      E.equiv (Multiplicative.ofAdd v)
    have hcoord : (E.kernelCoordinates
        (R.innerQuotientMap N) (R.innerSectionModule N) y).toAdd = v := by
      change (E.equiv.symm (E.equiv (Multiplicative.ofAdd v))).toAdd = v
      rw [E.equiv.symm_apply_apply]
      rfl
    have hy : y ∈ L := by
      apply (sectionSubgroupImage_mem_iff (p := 2)
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
    have hkFixed : (k : R.frame.top.range) ∈
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
      exact (R.secondFrame.bits_mem_ambientAxis _ k).2 hkFixed
    refine ⟨b, hb, ?_⟩
    change (R.secondFrame.normalSpace (R.outerTopNormal N.1)).mkQ b = v
    rw [show (b : R.secondFrame.kernelSpace) = x from hxk, hx]

/-- The literal natural quotient over the selected catalogue top is the
inflation of the actual inner omega image from the corresponding quotient
top. -/
noncomputable def innerNestedQuotientEquivInnerOmegaInflation
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    (nestedQuotientRepresentation
      (R.moduleAxis N) (R.innerOmegaNaturalAxis N)
      (R.moduleAxis_le_innerOmegaNaturalAxis N)).Equiv
      ((R.innerOmegaSubrepresentation N).toRepresentation.comp
        (QuotientGroup.mk' (R.topNormal N.1))) := by
  let tau := nestedQuotientRepresentation
    (R.moduleAxis N) (R.innerOmegaNaturalAxis N)
    (R.moduleAxis_le_innerOmegaNaturalAxis N)
  let I := intertwinerImage
    R.secondFrame.kernelTopPermutationSubrepresentation.toRepresentation
    (R.secondFrame.sectionTopRepresentation (R.outerTopNormal N.1))
    (R.secondFrame.sectionTopIntertwiner (R.outerTopNormal N.1))
    (nestedSubrepresentation (R.innerOmegaCoordinateAxis N)
      R.secondFrame.kernelTopPermutationSubrepresentation
      (R.innerOmegaCoordinateAxis_le_kernelTop N))
  let e0 : Representation.Equiv tau
      ((tau.comp R.topEquiv.symm.toMonoidHom).comp
        R.topEquiv.toMonoidHom) :=
    Representation.Equiv.mk (LinearEquiv.refl _ _) (by
      intro g
      apply LinearMap.ext
      intro v
      change tau g v = tau (R.topEquiv.symm (R.topEquiv g)) v
      rw [R.topEquiv.symm_apply_apply])
  let e1base := R.innerNestedQuotientSectionImageEquiv N
  let e1 : Representation.Equiv ((tau.comp R.topEquiv.symm.toMonoidHom).comp
      R.topEquiv.toMonoidHom)
      (I.toRepresentation.comp R.topEquiv.toMonoidHom) :=
    Representation.Equiv.mk e1base.toLinearEquiv
      (fun g ↦ e1base.isIntertwining' (R.topEquiv g))
  have hI : I.toSubmodule =
      (R.innerOmegaSubrepresentation N).toSubmodule :=
    R.innerSectionImage_toSubmodule_eq_innerOmega N
  let e2Linear : I.toSubmodule ≃ₗ[ZMod 2]
      (R.innerOmegaSubrepresentation N).toSubmodule := {
    toFun := fun v ↦ ⟨v.1, hI ▸ v.2⟩
    invFun := fun v ↦ ⟨v.1, hI.symm ▸ v.2⟩
    left_inv v := Subtype.ext rfl
    right_inv v := Subtype.ext rfl
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  let eFull := R.secondFrame.sectionTopEquivLiteralSectionInflation
    R.topEquiv (R.outerTopNormal N.1)
  let e2 : Representation.Equiv (I.toRepresentation.comp R.topEquiv.toMonoidHom)
      ((R.innerOmegaSubrepresentation N).toRepresentation.comp
        (QuotientGroup.mk' (R.topNormal N.1))) :=
    Representation.Equiv.mk e2Linear (by
      intro g
      apply LinearMap.ext
      intro v
      apply Subtype.ext
      exact LinearMap.congr_fun (eFull.isIntertwining' g) v.1)
  exact e0.trans (e1.trans e2)

end DegreeTwoPairTopTowerRealization
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
