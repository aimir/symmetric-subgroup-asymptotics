import SymmetricSubgroupAsymptotics.BinaryPairLiteralTopQuotient
import SymmetricSubgroupAsymptotics.BinaryPairCoupledCommutator
import SymmetricSubgroupAsymptotics.BinaryPairPermutationGeneratorExtension
import SymmetricSubgroupAsymptotics.CompositeKernelExact
import SymmetricSubgroupAsymptotics.NormalKernelCentralOmega
import SymmetricSubgroupAsymptotics.OriginalKernelNormalSubrepresentation
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopOriginalNormalSignature
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopStructuralAnchor

/-!
# The direct quotient map for two successive pair frames

A paired-eight count-sixteen row has two elementary binary kernels between
the original action and its literal degree-eight top.  This file constructs
the single map from every original quotient to the selected literal-top
quotient and proves that its whole direct quartet kernel is a binary group.
No splitting of either pair extension is chosen.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoPairTopTowerRealization

attribute [instance] outerTopNormal_normal topNormal_normal

variable {s t : ℕ} {D : DegreeTwoPairTopFiniteInterface t}
  {p : PreE7PairActionClass s}
  (R : DegreeTwoPairTopTowerRealization D p)

/-- The first pair quotient, with the actual image of `N` as denominator. -/
noncomputable def outerQuotientMap
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    (preE7PairAction s p ⧸ N.1) →*
      (R.frame.top.range ⧸ R.outerTopNormal N.1) := by
  letI : N.1.Normal := N.2
  let f : preE7PairAction s p →*
      (R.frame.top.range ⧸ R.outerTopNormal N.1) :=
    (QuotientGroup.mk' (R.outerTopNormal N.1)).comp
      R.frame.top.rangeRestrict
  apply QuotientGroup.lift N.1 f
  intro u hu
  apply MonoidHom.mem_ker.mpr
  apply (QuotientGroup.eq_one_iff _).mpr
  exact ⟨u, hu, rfl⟩

@[simp] theorem outerQuotientMap_apply
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal})
    (u : preE7PairAction s p) :
    R.outerQuotientMap N (QuotientGroup.mk' N.1 u) =
      QuotientGroup.mk' (R.outerTopNormal N.1)
        (R.frame.top.rangeRestrict u) :=
  rfl

theorem outerQuotientMap_surjective
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    Function.Surjective (R.outerQuotientMap N) := by
  letI : N.1.Normal := N.2
  intro q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective
    (R.outerTopNormal N.1) q
  obtain ⟨u, rfl⟩ := R.frame.top.rangeRestrict_surjective g
  exact ⟨QuotientGroup.mk' N.1 u, rfl⟩

private theorem outerTop_mem_normal_iff
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal})
    (u : preE7PairAction s p) :
    R.frame.top.rangeRestrict u ∈ R.outerTopNormal N.1 ↔
      u ∈ R.frame.top.ker ⊔ N.1 := by
  constructor
  · rintro ⟨n, hn, hnu⟩
    have hk : n⁻¹ * u ∈ R.frame.top.ker := by
      have heq := congrArg (fun a : R.frame.top.range =>
        (a : Equiv.Perm (Fin s))) hnu
      change R.frame.top n = R.frame.top u at heq
      rw [MonoidHom.mem_ker, map_mul, map_inv, heq, inv_mul_cancel]
    have hn' : n ∈ R.frame.top.ker ⊔ N.1 :=
      Subgroup.mem_sup_right hn
    have hk' : n⁻¹ * u ∈ R.frame.top.ker ⊔ N.1 :=
      Subgroup.mem_sup_left hk
    simpa using (R.frame.top.ker ⊔ N.1).mul_mem hn' hk'
  · intro hu
    letI : N.1.Normal := N.2
    obtain ⟨k, hk, n, hn, hkn⟩ :=
      Subgroup.mem_sup_of_normal_right.mp hu
    refine ⟨n, hn, ?_⟩
    have hk' : R.frame.top.rangeRestrict k = 1 :=
      Subtype.ext (MonoidHom.mem_ker.mp hk)
    rw [← hkn, map_mul, hk', one_mul]

theorem outerQuotientMap_ker_eq_zeroCutBase_ker
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    (R.outerQuotientMap N).ker = (R.frame.zeroCutBase N.1).ker := by
  letI : N.1.Normal := N.2
  ext q
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective N.1 q
  simp only [MonoidHom.mem_ker, R.outerQuotientMap_apply,
    R.frame.zeroCutBase_apply]
  change ((R.frame.top.rangeRestrict u :
      R.frame.top.range ⧸ R.outerTopNormal N.1) = 1) ↔
    ((u : preE7PairAction s p ⧸ (R.frame.top.ker ⊔ N.1)) = 1)
  rw [QuotientGroup.eq_one_iff, QuotientGroup.eq_one_iff]
  exact R.outerTop_mem_normal_iff N u

theorem outerQuotientMap_kernel_isPGroup
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    IsPGroup 2 (R.outerQuotientMap N).ker := by
  letI : N.1.Normal := N.2
  rw [R.outerQuotientMap_ker_eq_zeroCutBase_ker N]
  have hmodule : IsPGroup 2 (Multiplicative (R.frame.zeroCutModule N.1)) :=
    primeModule_isPGroup 2 (R.frame.zeroCutModule N.1)
  exact hmodule.of_equiv (R.frame.zeroCutKernelEquiv N.1)

/-- The second pair quotient, transported to the literal degree-`t` top. -/
noncomputable def innerQuotientMap
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    (R.frame.top.range ⧸ R.outerTopNormal N.1) →*
      (D.top ⧸ R.topNormal N.1) := by
  letI : N.1.Normal := N.2
  letI : (R.outerTopNormal N.1).Normal := R.outerTopNormal_normal N.1
  exact R.secondFrame.literalTopQuotientMap R.topEquiv
    (R.outerTopNormal N.1)

theorem innerQuotientMap_surjective
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    Function.Surjective (R.innerQuotientMap N) := by
  letI : N.1.Normal := N.2
  letI : (R.outerTopNormal N.1).Normal := R.outerTopNormal_normal N.1
  exact R.secondFrame.literalTopQuotientMap_surjective R.topEquiv
    (R.outerTopNormal N.1)

theorem innerQuotientMap_kernel_isPGroup
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    IsPGroup 2 (R.innerQuotientMap N).ker := by
  letI : N.1.Normal := N.2
  letI : (R.outerTopNormal N.1).Normal := R.outerTopNormal_normal N.1
  exact R.secondFrame.literalTopQuotientMap_kernel_isPGroup R.topEquiv
    (R.outerTopNormal N.1)

/-- Literal module coordinates on the second zero-cut kernel. -/
noncomputable def innerZeroCutKernelEquiv
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    Multiplicative
        (R.secondFrame.zeroCutModule (R.outerTopNormal N.1)) ≃*
      (R.innerQuotientMap N).ker := by
  letI : N.1.Normal := N.2
  letI : (R.outerTopNormal N.1).Normal := R.outerTopNormal_normal N.1
  exact (R.secondFrame.zeroCutKernelEquiv (R.outerTopNormal N.1)).trans
    (MulEquiv.subgroupCongr
      (R.secondFrame.literalTopQuotientMap_ker_eq_zeroCutBase_ker
        R.topEquiv (R.outerTopNormal N.1)).symm)

/-- The second zero-cut module with the selected literal top quotient as its
acting group. -/
def innerZeroCutModule
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    Rep (ZMod 2) (D.top ⧸ R.topNormal N.1) := by
  letI : N.1.Normal := N.2
  letI : (R.outerTopNormal N.1).Normal := R.outerTopNormal_normal N.1
  exact R.secondFrame.literalZeroCutModule R.topEquiv
    (R.outerTopNormal N.1)

/-- Module chart for the second layer in the selected literal quotient. -/
noncomputable def innerZeroCutModuleChart
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    OriginalKernelModuleChart (R.innerQuotientMap N)
      (R.innerZeroCutModule N) := by
  letI : N.1.Normal := N.2
  letI : (R.outerTopNormal N.1).Normal := R.outerTopNormal_normal N.1
  exact R.secondFrame.literalZeroCutModuleChart R.topEquiv
    (R.outerTopNormal N.1)

/-- The direct second section module, before the harmless quotient by zero. -/
def innerSectionModule
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    Rep (ZMod 2) (D.top ⧸ R.topNormal N.1) := by
  letI : N.1.Normal := N.2
  letI : (R.outerTopNormal N.1).Normal := R.outerTopNormal_normal N.1
  exact R.secondFrame.literalSectionModule R.topEquiv
    (R.outerTopNormal N.1)

noncomputable def innerSectionModuleChart
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    OriginalKernelModuleChart (R.innerQuotientMap N)
      (R.innerSectionModule N) := by
  letI : N.1.Normal := N.2
  letI : (R.outerTopNormal N.1).Normal := R.outerTopNormal_normal N.1
  exact R.secondFrame.literalSectionModuleChart R.topEquiv
    (R.outerTopNormal N.1)

/-- The direct map through both pair quotients before replacing the selected
normal by its equal finite-registry state. -/
noncomputable def rawQuotientMap
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    (preE7PairAction s p ⧸ N.1) →* (D.top ⧸ R.topNormal N.1) :=
  (R.innerQuotientMap N).comp (R.outerQuotientMap N)

/-- The direct-kernel central omega lifted to an actual normal subgroup of
the original quotient. -/
def rawKernelOmegaLift
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    Subgroup (preE7PairAction s p ⧸ N.1) :=
  normalKernelCentralOmega (R.rawQuotientMap N)

instance rawKernelOmegaLift_normal
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    (R.rawKernelOmegaLift N).Normal :=
  normalKernelCentralOmega_normal (R.rawQuotientMap N)

/-- The lifted ambient subgroup retains exactly the central involution
module of the direct kernel. -/
noncomputable def rawKernelOmegaEquiv
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    binaryCentralOmega (R.rawQuotientMap N).ker ≃*
      R.rawKernelOmegaLift N :=
  binaryCentralOmegaEquivNormalKernel (R.rawQuotientMap N)

/-- Preimage of the lifted omega subgroup in the original action. -/
def rawKernelOmegaOriginalPreimage
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    Subgroup (preE7PairAction s p) := by
  letI : N.1.Normal := N.2
  exact (R.rawKernelOmegaLift N).comap (QuotientGroup.mk' N.1)

instance rawKernelOmegaOriginalPreimage_normal
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    (R.rawKernelOmegaOriginalPreimage N).Normal := by
  letI : N.1.Normal := N.2
  exact Subgroup.Normal.comap inferInstance (QuotientGroup.mk' N.1)

/-- The original denominator is contained in the pullback of direct-kernel
omega.  This is the inclusion needed to turn omega centrality downstairs
into literal commutator containment upstairs. -/
theorem originalNormal_le_rawKernelOmegaOriginalPreimage
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    N.1 ≤ R.rawKernelOmegaOriginalPreimage N := by
  intro u hu
  change QuotientGroup.mk' N.1 u ∈ R.rawKernelOmegaLift N
  rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff _).mpr hu]
  exact Subgroup.one_mem _

/-- Two elements in the original pullback of direct-kernel omega commute
modulo the original denominator. -/
theorem rawKernelOmegaOriginalPreimage_commutator_mem
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal})
    (u : preE7PairAction s p)
    (hu : u ∈ R.rawKernelOmegaOriginalPreimage N)
    (k : R.frame.top.ker)
    (hk : (k : preE7PairAction s p) ∈
      R.rawKernelOmegaOriginalPreimage N) :
    ((k : preE7PairAction s p)⁻¹ * u * k * u⁻¹) ∈ N.1 := by
  letI : N.1.Normal := N.2
  let q := QuotientGroup.mk' N.1
  have huOmega : q u ∈ R.rawKernelOmegaLift N := hu
  have hkOmega : q (k : preE7PairAction s p) ∈
      R.rawKernelOmegaLift N := hk
  have hcomm : Commute (q u) (q (k : preE7PairAction s p)) :=
    huOmega.2.1 ⟨q (k : preE7PairAction s p), hkOmega.1⟩
  apply (QuotientGroup.eq_one_iff _).mp
  change q ((k : preE7PairAction s p)⁻¹ * u * k * u⁻¹) = 1
  simp only [map_mul, map_inv]
  calc
    (q (k : preE7PairAction s p))⁻¹ * q u *
          q (k : preE7PairAction s p) * (q u)⁻¹ =
        (q (k : preE7PairAction s p))⁻¹ *
          q (k : preE7PairAction s p) * q u * (q u)⁻¹ := by
            simpa only [mul_assoc] using congrArg
              (fun v => (q (k : preE7PairAction s p))⁻¹ * v * (q u)⁻¹)
              hcomm.eq
    _ = 1 := by group

/-- The intersection of lifted omega with the first pair kernel, in the
literal sixteen-coordinate module. -/
def outerOmegaAxis
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    Subrepresentation
      (permutationFunctionRepresentation (ZMod 2)
        R.frame.top.range (Fin s)) :=
  R.frame.sharedOriginalAxis
    (permutationFunctionRepresentation (ZMod 2)
      R.frame.top.range (Fin s))
    (MulEquiv.refl R.frame.top.range) (fun _ _ => rfl)
    (R.rawKernelOmegaOriginalPreimage N)

/-- Image of the lifted omega subgroup in the intermediate pair top. -/
def rawKernelOmegaTopImage
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    Subgroup (R.frame.top.range ⧸ R.outerTopNormal N.1) :=
  (R.rawKernelOmegaLift N).map (R.outerQuotientMap N)

instance rawKernelOmegaTopImage_normal
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    (R.rawKernelOmegaTopImage N).Normal :=
  Subgroup.Normal.map inferInstance _ (R.outerQuotientMap_surjective N)

theorem rawKernelOmegaTopImage_le_innerKernel
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    R.rawKernelOmegaTopImage N ≤ (R.innerQuotientMap N).ker := by
  rintro y ⟨x, hx, rfl⟩
  apply MonoidHom.mem_ker.mpr
  simpa only [rawQuotientMap, MonoidHom.comp_apply] using
    MonoidHom.mem_ker.mp hx.1

/-- Preimage of the intermediate omega image before quotienting by the
original normal image. -/
def rawKernelOmegaIntermediatePreimage
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    Subgroup R.frame.top.range := by
  letI : N.1.Normal := N.2
  letI : (R.outerTopNormal N.1).Normal := R.outerTopNormal_normal N.1
  exact (R.rawKernelOmegaTopImage N).comap
    (QuotientGroup.mk' (R.outerTopNormal N.1))

/-- Pulling the omega image back from the intermediate quotient gives
exactly the first-top image of its original pullback.  The reverse inclusion
uses that the original denominator is already contained in that pullback. -/
theorem rawKernelOmegaIntermediatePreimage_eq_map
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    R.rawKernelOmegaIntermediatePreimage N =
      (R.rawKernelOmegaOriginalPreimage N).map
        R.frame.top.rangeRestrict := by
  letI : N.1.Normal := N.2
  letI : (R.outerTopNormal N.1).Normal := R.outerTopNormal_normal N.1
  ext y
  constructor
  · intro hy
    change QuotientGroup.mk' (R.outerTopNormal N.1) y ∈
      (R.rawKernelOmegaLift N).map (R.outerQuotientMap N) at hy
    obtain ⟨q, hq, hqy⟩ := hy
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective N.1 q
    rw [R.outerQuotientMap_apply] at hqy
    have hdiv : R.frame.top.rangeRestrict u / y ∈
        R.outerTopNormal N.1 :=
      QuotientGroup.eq_iff_div_mem.mp hqy
    obtain ⟨n, hn, hntop⟩ := hdiv
    have hnOmega : n ∈ R.rawKernelOmegaOriginalPreimage N :=
      R.originalNormal_le_rawKernelOmegaOriginalPreimage N hn
    refine ⟨n⁻¹ * u,
      (R.rawKernelOmegaOriginalPreimage N).mul_mem
        ((R.rawKernelOmegaOriginalPreimage N).inv_mem hnOmega) hq, ?_⟩
    rw [map_mul, map_inv, hntop]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, mul_assoc,
      inv_mul_cancel, mul_one]
  · rintro ⟨u, hu, rfl⟩
    change QuotientGroup.mk' (R.outerTopNormal N.1)
        (R.frame.top.rangeRestrict u) ∈
      (R.rawKernelOmegaLift N).map (R.outerQuotientMap N)
    exact ⟨QuotientGroup.mk' N.1 u, hu, rfl⟩

/-- The original normal image is contained in the intermediate pullback of
the direct-kernel omega image. -/
theorem outerTopNormal_le_rawKernelOmegaIntermediatePreimage
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    R.outerTopNormal N.1 ≤ R.rawKernelOmegaIntermediatePreimage N := by
  rw [R.rawKernelOmegaIntermediatePreimage_eq_map N]
  exact Subgroup.map_mono (R.originalNormal_le_rawKernelOmegaOriginalPreimage N)

instance rawKernelOmegaIntermediatePreimage_normal
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    (R.rawKernelOmegaIntermediatePreimage N).Normal := by
  letI : N.1.Normal := N.2
  letI : (R.outerTopNormal N.1).Normal := R.outerTopNormal_normal N.1
  exact Subgroup.Normal.comap inferInstance
    (QuotientGroup.mk' (R.outerTopNormal N.1))

/-- The top layer `K` in the paper, lifted to the natural eight-coordinate
module used by the finite coupled registry. -/
def innerOmegaNaturalAxis
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    Subrepresentation
      (permutationFunctionRepresentation (ZMod 2) D.top (Fin t)) :=
  R.secondFrame.sharedOriginalAxis
    (permutationFunctionRepresentation (ZMod 2) D.top (Fin t))
    R.topEquiv R.module_action_eq
    (R.rawKernelOmegaIntermediatePreimage N)

/-- The same numerator before transporting the second-frame top to the
literal catalogue top. -/
def innerOmegaCoordinateAxis
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    Subrepresentation R.secondFrame.coordinateTopAction :=
  R.secondFrame.sharedOriginalAxis
    R.secondFrame.coordinateTopAction (MulEquiv.refl _)
    (fun _ _ ↦ rfl) (R.rawKernelOmegaIntermediatePreimage N)

/-- The denominator axis before transport to the literal catalogue top. -/
def innerNormalCoordinateAxis
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    Subrepresentation R.secondFrame.coordinateTopAction :=
  R.secondFrame.sharedOriginalAxis
    R.secondFrame.coordinateTopAction (MulEquiv.refl _)
    (fun _ _ ↦ rfl) (R.outerTopNormal N.1)

theorem innerNormalCoordinateAxis_le_innerOmegaCoordinateAxis
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    R.innerNormalCoordinateAxis N ≤ R.innerOmegaCoordinateAxis N := by
  intro v hv
  change v ∈ R.secondFrame.ambientAxis
    (R.rawKernelOmegaIntermediatePreimage N)
  change v ∈ R.secondFrame.ambientAxis (R.outerTopNormal N.1) at hv
  obtain ⟨k, hk, rfl⟩ := (R.secondFrame.mem_ambientAxis _ v).1 hv
  exact (R.secondFrame.mem_ambientAxis _ _).2
    ⟨k, R.outerTopNormal_le_rawKernelOmegaIntermediatePreimage N hk, rfl⟩

theorem innerOmegaCoordinateAxis_le_kernelTop
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    R.innerOmegaCoordinateAxis N ≤
      R.secondFrame.kernelTopPermutationSubrepresentation :=
  R.secondFrame.ambientAxis_le_kernelSpace
    (R.rawKernelOmegaIntermediatePreimage N)

theorem innerNormalCoordinateAxis_eq_normalTopPermutation
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    R.innerNormalCoordinateAxis N =
      R.secondFrame.normalTopPermutationSubrepresentation
        (R.outerTopNormal N.1) := by
  apply Subrepresentation.toSubmodule_injective
  change R.secondFrame.ambientAxis (R.outerTopNormal N.1) =
    (R.secondFrame.normalSpace (R.outerTopNormal N.1)).map
      R.secondFrame.kernelSpace.subtype
  exact (R.secondFrame.normalSpace_map_subtype_eq_ambientAxis
    (R.outerTopNormal N.1)).symm

theorem innerOmegaCoordinateAxis_toSubmodule
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    (R.innerOmegaCoordinateAxis N).toSubmodule =
      (R.innerOmegaNaturalAxis N).toSubmodule :=
  rfl

theorem innerOmegaNaturalAxis_toSubmodule
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    (R.innerOmegaNaturalAxis N).toSubmodule =
      R.secondFrame.ambientAxis
        ((R.rawKernelOmegaOriginalPreimage N).map
          R.frame.top.rangeRestrict) := by
  change R.secondFrame.ambientAxis
      (R.rawKernelOmegaIntermediatePreimage N) = _
  rw [R.rawKernelOmegaIntermediatePreimage_eq_map N]

/-- Pair-sum image of the first-layer omega intersection, before descending
from the intermediate group to its top range. -/
def outerOmegaPairSumPullbackAxis
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    Subrepresentation R.secondFrame.pulledBackCoordinateTopAction :=
  intertwinerImage
    (permutationFunctionRepresentation (ZMod 2)
      R.frame.top.range (Fin s))
    R.secondFrame.pulledBackCoordinateTopAction
    R.secondFrame.pairSumIntertwiner (R.outerOmegaAxis N)

/-- Pair-constant preimage of the first-layer omega intersection, before
descending to the intermediate top range. -/
def outerOmegaConstantPullbackAxis
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    Subrepresentation R.secondFrame.pulledBackCoordinateTopAction :=
  intertwinerPreimage
    R.secondFrame.pulledBackCoordinateTopAction
    (permutationFunctionRepresentation (ZMod 2)
      R.frame.top.range (Fin s))
    R.secondFrame.pairConstantIntertwiner (R.outerOmegaAxis N)

/-- Transport a natural axis on the intermediate pair top to the selected
literal degree-eight top. -/
def transportInnerNaturalAxis
    (M : Subrepresentation R.secondFrame.coordinateTopAction) :
    Subrepresentation
      (permutationFunctionRepresentation (ZMod 2) D.top (Fin t)) where
  toSubmodule := M.toSubmodule
  apply_mem_toSubmodule g v hv := by
    rw [R.module_action_eq]
    exact M.apply_mem_toSubmodule (R.topEquiv g) hv

/-- The middle layer `W = (B+C)/C`, expressed by pair-sum. -/
def outerOmegaPairSumAxis
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    Subrepresentation
      (permutationFunctionRepresentation (ZMod 2) D.top (Fin t)) :=
  R.transportInnerNaturalAxis
    (R.secondFrame.descendPulledBackSubrepresentation
      (R.outerOmegaPairSumPullbackAxis N))

/-- The bottom layer `L = B ∩ C`, expressed in pair-constant coordinates. -/
def outerOmegaConstantAxis
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    Subrepresentation
      (permutationFunctionRepresentation (ZMod 2) D.top (Fin t)) :=
  R.transportInnerNaturalAxis
    (R.secondFrame.descendPulledBackSubrepresentation
      (R.outerOmegaConstantPullbackAxis N))

theorem outerOmegaPairSumAxis_toSubmodule
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    (R.outerOmegaPairSumAxis N).toSubmodule =
      (R.frame.ambientAxis (R.rawKernelOmegaOriginalPreimage N)).map
        R.secondFrame.pairSum :=
  rfl

theorem outerOmegaConstantAxis_toSubmodule
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    (R.outerOmegaConstantAxis N).toSubmodule =
      (R.frame.ambientAxis (R.rawKernelOmegaOriginalPreimage N)).comap
        R.secondFrame.pairConstant :=
  rfl

/-- The three actual omega axes satisfy the product containment consumed by
the generated coupled-head registry.  No finite census identification is
used here: this is the literal two-frame commutator calculation. -/
theorem omegaAxes_productSpan_le
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    binaryCoordinateProductSpan
        (R.innerOmegaNaturalAxis N).toSubmodule
        (R.outerOmegaPairSumAxis N).toSubmodule ≤
      (R.outerOmegaConstantAxis N).toSubmodule := by
  rw [R.innerOmegaNaturalAxis_toSubmodule N,
    R.outerOmegaPairSumAxis_toSubmodule N,
    R.outerOmegaConstantAxis_toSubmodule N]
  exact R.frame.nestedPair_productSpan_le_constantPreimage
    R.secondFrame N.1 (R.rawKernelOmegaOriginalPreimage N)
    (R.originalNormal_le_rawKernelOmegaOriginalPreimage N)
    (R.rawKernelOmegaOriginalPreimage_commutator_mem N)

/-- The actual image of direct-kernel omega in the second zero-cut module.
It is invariant under the selected literal top quotient because the lifted
omega subgroup is normal in the original quotient. -/
def innerOmegaSubrepresentation
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    Subrepresentation (R.innerSectionModule N).ρ :=
  (R.innerSectionModuleChart N).normalSubrepresentation
    (R.innerQuotientMap N) (R.innerQuotientMap_surjective N)
    (R.innerSectionModule N) (R.rawKernelOmegaTopImage N)

/-- The first map in the exact two-layer filtration of the direct quartet
kernel.  Its target is the actual second zero-cut kernel. -/
def rawKernelProjection
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    (R.rawQuotientMap N).ker →* (R.innerQuotientMap N).ker :=
  compositeKernelProjection (R.outerQuotientMap N) (R.innerQuotientMap N)

/-- Project the intrinsic central omega of the direct two-frame kernel onto
the actual second-frame kernel.  This is the group-level first map in the
omega filtration; no abstract replacement of either kernel is made. -/
def rawKernelOmegaProjection
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    binaryCentralOmega (R.rawQuotientMap N).ker →*
      (R.innerQuotientMap N).ker :=
  (R.rawKernelProjection N).comp
    (binaryCentralOmegaEmbedding (G := (R.rawQuotientMap N).ker))

@[simp] theorem rawKernelOmegaEquiv_val
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal})
    (z : binaryCentralOmega (R.rawQuotientMap N).ker) :
    ((R.rawKernelOmegaEquiv N z : R.rawKernelOmegaLift N) :
        preE7PairAction s p ⧸ N.1) =
      ((binaryCentralOmegaEmbedding z : (R.rawQuotientMap N).ker) :
        preE7PairAction s p ⧸ N.1) :=
  rfl

/-- The image of intrinsic direct-kernel omega under the filtration map is
exactly the previously constructed intermediate omega image. -/
theorem rawKernelOmegaProjection_range_eq
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    (R.rawKernelOmegaProjection N).range =
      (R.rawKernelOmegaTopImage N).subgroupOf (R.innerQuotientMap N).ker := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨(R.rawKernelOmegaEquiv N z :
        preE7PairAction s p ⧸ N.1),
      (R.rawKernelOmegaEquiv N z).property, rfl⟩
  · intro hy
    change (y : R.frame.top.range ⧸ R.outerTopNormal N.1) ∈
      R.rawKernelOmegaTopImage N at hy
    obtain ⟨x, hx, hxy⟩ := hy
    let z := (R.rawKernelOmegaEquiv N).symm ⟨x, hx⟩
    have he := congrArg
      (fun a : R.rawKernelOmegaLift N =>
        (a : preE7PairAction s p ⧸ N.1))
      ((R.rawKernelOmegaEquiv N).apply_symm_apply ⟨x, hx⟩)
    change ((binaryCentralOmegaEmbedding z : (R.rawQuotientMap N).ker) :
      preE7PairAction s p ⧸ N.1) = x at he
    refine ⟨z, Subtype.ext ?_⟩
    change R.outerQuotientMap N
      ((binaryCentralOmegaEmbedding z : (R.rawQuotientMap N).ker) :
        preE7PairAction s p ⧸ N.1) = _
    rw [he]
    exact hxy

/-- Additive coordinates for the projected direct-kernel omega inside the
literal second section module. -/
noncomputable def rawKernelOmegaInnerSectionMap
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    Additive (binaryCentralOmega (R.rawQuotientMap N).ker) →ₗ[ZMod 2]
      R.innerSectionModule N :=
  (AddMonoidHom.toMultiplicativeRight.symm
    ((R.innerSectionModuleChart N).equiv.symm.toMonoidHom.comp
      (R.rawKernelOmegaProjection N))).toZModLinearMap 2

@[simp] theorem rawKernelOmegaInnerSectionMap_apply
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal})
    (z : binaryCentralOmega (R.rawQuotientMap N).ker) :
    R.rawKernelOmegaInnerSectionMap N (Additive.ofMul z) =
      ((R.innerSectionModuleChart N).kernelCoordinates
        (R.innerQuotientMap N) (R.innerSectionModule N)
        (R.rawKernelOmegaProjection N z)).toAdd :=
  rfl

/-- The linear range in second-section coordinates is precisely the actual
inner omega subrepresentation.  This upgrades the group-level image
identity to the literal module used by the top action. -/
theorem rawKernelOmegaInnerSectionMap_range_eq
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    LinearMap.range (R.rawKernelOmegaInnerSectionMap N) =
      (R.innerOmegaSubrepresentation N).toSubmodule := by
  let E := R.innerSectionModuleChart N
  let L := (R.rawKernelOmegaTopImage N).subgroupOf
    (R.innerQuotientMap N).ker
  have hL : (R.rawKernelOmegaProjection N).range = L :=
    R.rawKernelOmegaProjection_range_eq N
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
  · rintro ⟨z, rfl⟩
    change ((E.kernelCoordinates
      (R.innerQuotientMap N) (R.innerSectionModule N)
      (R.rawKernelOmegaProjection N z.toMul)).toAdd) ∈
        E.normalSpace (R.innerQuotientMap N)
          (R.innerSectionModule N) (R.rawKernelOmegaTopImage N)
    apply (sectionSubgroupImage_mem_iff (p := 2)
      (E.kernelCoordinates (R.innerQuotientMap N)
        (R.innerSectionModule N)) L hker
      (R.rawKernelOmegaProjection N z.toMul)).2
    rw [← hL]
    exact ⟨z.toMul, rfl⟩
  · intro hv
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
      change v ∈ E.normalSpace (R.innerQuotientMap N)
        (R.innerSectionModule N) (R.rawKernelOmegaTopImage N) at hv
      rwa [hcoord]
    have hyrange : y ∈ (R.rawKernelOmegaProjection N).range := by
      rw [hL]
      exact hy
    obtain ⟨z, hz⟩ := hyrange
    refine ⟨Additive.ofMul z, ?_⟩
    rw [R.rawKernelOmegaInnerSectionMap_apply N z, hz, hcoord]

theorem rawKernelProjection_surjective
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    Function.Surjective (R.rawKernelProjection N) :=
  compositeKernelProjection_surjective
    (R.outerQuotientMap N) (R.innerQuotientMap N)
    (R.outerQuotientMap_surjective N)

/-- The kernel of the first filtration map is canonically the actual first
zero-cut kernel. -/
noncomputable def outerKernelEquivRawKernelProjectionKer
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    (R.outerQuotientMap N).ker ≃* (R.rawKernelProjection N).ker :=
  compositeKernelFiberEquiv
    (R.outerQuotientMap N) (R.innerQuotientMap N)

/-- Literal module coordinates on the first kernel, now regarded as the
kernel of the direct-kernel projection. -/
noncomputable def outerZeroCutKernelEquivRawKernelProjectionKer
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    Multiplicative (R.frame.zeroCutModule N.1) ≃*
      (R.rawKernelProjection N).ker :=
  (R.frame.zeroCutKernelEquiv N.1).trans
    ((MulEquiv.subgroupCongr
      (R.outerQuotientMap_ker_eq_zeroCutBase_ker N).symm).trans
        (R.outerKernelEquivRawKernelProjectionKer N))

@[simp] theorem outerZeroCutKernelEquivRawKernelProjectionKer_val
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal})
    (l : R.frame.top.ker) :
    ((((R.outerZeroCutKernelEquivRawKernelProjectionKer N)
          (R.frame.zeroCutMap N.1 l) :
        (R.rawKernelProjection N).ker) :
      (R.rawQuotientMap N).ker) :
        preE7PairAction s p ⧸ N.1) =
      QuotientGroup.mk' N.1 (l : preE7PairAction s p) := by
  change ((R.frame.zeroCutKernelEquiv N.1 (R.frame.zeroCutMap N.1 l)) :
    preE7PairAction s p ⧸ N.1) = _
  exact congrArg (fun y : (R.frame.zeroCutBase N.1).ker =>
    (y : preE7PairAction s p ⧸ N.1))
    (R.frame.zeroCutKernelEquiv_apply N.1 l)

/-- Elements of direct-kernel omega killed by the second-kernel projection
lie literally in the first kernel of the two-frame extension. -/
def rawKernelOmegaOuterInclusion
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    (R.rawKernelOmegaProjection N).ker →*
      (R.rawKernelProjection N).ker where
  toFun z :=
    ⟨binaryCentralOmegaEmbedding z.1, z.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem rawKernelOmegaOuterInclusion_injective
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    Function.Injective (R.rawKernelOmegaOuterInclusion N) := by
  intro z w hzw
  apply Subtype.ext
  apply binaryCentralOmegaEmbedding_injective
  exact congrArg (fun x : (R.rawKernelProjection N).ker =>
    (x : (R.rawQuotientMap N).ker)) hzw

/-- Every subgroup of central omega is an elementary binary module. -/
instance rawKernelOmegaProjectionKernel_module
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    Module (ZMod 2) (Additive (R.rawKernelOmegaProjection N).ker) :=
  AddCommGroup.zmodModule (n := 2) (fun z => by
    apply Additive.toMul.injective
    apply Subtype.ext
    change (z.toMul.1) ^ 2 = 1
    apply Subtype.ext
    exact z.toMul.1.property)

/-- Literal first zero-cut coordinates on the kernel of the omega
projection. -/
noncomputable def rawKernelOmegaOuterCoordinateMap
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    Additive (R.rawKernelOmegaProjection N).ker →ₗ[ZMod 2]
      R.frame.zeroCutModule N.1 :=
  (AddMonoidHom.toMultiplicativeRight.symm
    ((R.outerZeroCutKernelEquivRawKernelProjectionKer N).symm.toMonoidHom.comp
      (R.rawKernelOmegaOuterInclusion N))).toZModLinearMap 2

@[simp] theorem rawKernelOmegaOuterCoordinateMap_apply
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal})
    (z : Additive (R.rawKernelOmegaProjection N).ker) :
    R.rawKernelOmegaOuterCoordinateMap N z =
      ((R.outerZeroCutKernelEquivRawKernelProjectionKer N).symm
        (R.rawKernelOmegaOuterInclusion N z.toMul)).toAdd := rfl

theorem rawKernelOmegaOuterCoordinateMap_injective
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    Function.Injective (R.rawKernelOmegaOuterCoordinateMap N) := by
  intro z w hzw
  apply Additive.toMul.injective
  apply R.rawKernelOmegaOuterInclusion_injective N
  apply (R.outerZeroCutKernelEquivRawKernelProjectionKer N).symm.injective
  exact congrArg Multiplicative.ofAdd hzw

/-- The part of the first pair kernel lying in the original pullback of
direct-kernel omega. -/
abbrev outerOmegaRetainedKernel
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :=
  (R.rawKernelOmegaOriginalPreimage N).subgroupOf R.frame.top.ker

instance outerOmegaRetainedKernel_commGroup
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    CommGroup (R.outerOmegaRetainedKernel N) :=
  { (inferInstance : Group (R.outerOmegaRetainedKernel N)) with
    mul_comm := by
      intro x y
      apply Subtype.ext
      apply R.frame.bitsHom_injective
      change R.frame.bitsHom (x.1 * y.1) = R.frame.bitsHom (y.1 * x.1)
      rw [map_mul, map_mul, mul_comm] }

instance outerOmegaRetainedKernel_module
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    Module (ZMod 2) (Additive (R.outerOmegaRetainedKernel N)) :=
  AddCommGroup.zmodModule (n := 2) (fun z => by
    apply Additive.toMul.injective
    apply Subtype.ext
    apply R.frame.bitsHom_injective
    change R.frame.bitsHom (z.toMul.1 ^ 2) = R.frame.bitsHom 1
    rw [map_pow, map_one]
    apply Multiplicative.toAdd.injective
    change 2 • (R.frame.bitsHom z.toMul.1).toAdd = 0
    simp only [two_nsmul]
    funext i
    exact CharTwo.add_self_eq_zero ((R.frame.bitsHom z.toMul.1).toAdd i))

/-- Map the retained first-kernel omega intersection to the literal outer
zero-cut section. -/
noncomputable def outerOmegaZeroCutMap
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    Additive (R.outerOmegaRetainedKernel N) →ₗ[ZMod 2]
      R.frame.zeroCutModule N.1 :=
  (AddMonoidHom.toMultiplicativeRight.symm
    ((R.frame.zeroCutMap N.1).comp
      (R.outerOmegaRetainedKernel N).subtype)).toZModLinearMap 2

@[simp] theorem outerOmegaZeroCutMap_apply
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal})
    (l : Additive (R.outerOmegaRetainedKernel N)) :
    R.outerOmegaZeroCutMap N l =
      (R.frame.zeroCutMap N.1 l.toMul.1).toAdd := rfl

/-- Faithful bit coordinates identify the retained first-kernel omega
intersection with the actual outer omega axis used by the coupled table. -/
noncomputable def outerOmegaRetainedKernelEquivAxis
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    Additive (R.outerOmegaRetainedKernel N) ≃ₗ[ZMod 2]
      (R.outerOmegaAxis N).toSubmodule := by
  let f : Additive (R.outerOmegaRetainedKernel N) →ₗ[ZMod 2]
      (R.outerOmegaAxis N).toSubmodule :=
    ((AddMonoidHom.toMultiplicativeRight.symm
      (R.frame.bitsHom.comp (R.outerOmegaRetainedKernel N).subtype)).toZModLinearMap 2).codRestrict (R.outerOmegaAxis N).toSubmodule (fun l ↦ by
          exact (R.frame.bits_mem_ambientAxis
            (R.rawKernelOmegaOriginalPreimage N) l.toMul.1).2 l.toMul.2)
  apply LinearEquiv.ofBijective f
  constructor
  · intro l m hlm
    apply Additive.toMul.injective
    apply Subtype.ext
    exact R.frame.bitsHom_injective
      (congrArg (fun v : (R.outerOmegaAxis N).toSubmodule ↦
        Multiplicative.ofAdd (v : Fin s → ZMod 2)) hlm)
  · rintro ⟨v, hv⟩
    obtain ⟨l, hl, hlv⟩ := (R.frame.mem_ambientAxis
      (R.rawKernelOmegaOriginalPreimage N) v).1 hv
    let lOmega : R.outerOmegaRetainedKernel N := ⟨l, hl⟩
    refine ⟨Additive.ofMul lOmega, ?_⟩
    apply Subtype.ext
    exact hlv

set_option maxHeartbeats 1000000 in
/-- The outer coordinates of the omega-filtration kernel are exactly the
zero-cut image of the retained first-kernel intersection. -/
theorem rawKernelOmegaOuterCoordinateMap_range_eq
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    LinearMap.range (R.rawKernelOmegaOuterCoordinateMap N) =
      LinearMap.range (R.outerOmegaZeroCutMap N) := by
  ext a
  constructor
  · rintro ⟨z, rfl⟩
    let y : (R.rawKernelProjection N).ker :=
      R.rawKernelOmegaOuterInclusion N z.toMul
    let a0 : Multiplicative (R.frame.zeroCutModule N.1) :=
      (R.outerZeroCutKernelEquivRawKernelProjectionKer N).symm y
    have hlift : ∃ l : R.frame.top.ker, R.frame.zeroCutMap N.1 l = a0 :=
      R.frame.zeroCutMap_surjective N.1 a0
    obtain ⟨l, hl⟩ := hlift
    dsimp only [a0, y] at hl
    have hchart := congrArg
      (R.outerZeroCutKernelEquivRawKernelProjectionKer N) hl
    rw [(R.outerZeroCutKernelEquivRawKernelProjectionKer N).apply_symm_apply]
      at hchart
    have hval := congrArg
      (fun y : (R.rawKernelProjection N).ker ↦
        (((y : (R.rawQuotientMap N).ker) :
          preE7PairAction s p ⧸ N.1))) hchart
    dsimp only at hval
    have hlOmega : (l : preE7PairAction s p) ∈
        R.rawKernelOmegaOriginalPreimage N := by
      change QuotientGroup.mk' N.1 (l : preE7PairAction s p) ∈
        R.rawKernelOmegaLift N
      rw [← R.outerZeroCutKernelEquivRawKernelProjectionKer_val N l,
        hval]
      change ((binaryCentralOmegaEmbedding z.toMul.1 :
        (R.rawQuotientMap N).ker) : preE7PairAction s p ⧸ N.1) ∈
          R.rawKernelOmegaLift N
      exact (R.rawKernelOmegaEquiv N z.toMul.1).property
    let lOmega : R.outerOmegaRetainedKernel N := ⟨l, hlOmega⟩
    refine ⟨Additive.ofMul lOmega, ?_⟩
    rw [R.rawKernelOmegaOuterCoordinateMap_apply]
    exact congrArg Multiplicative.toAdd hl
  · rintro ⟨l, rfl⟩
    let q : preE7PairAction s p ⧸ N.1 :=
      QuotientGroup.mk' N.1
        (l.toMul.1 : preE7PairAction s p)
    have hqOmega : q ∈ R.rawKernelOmegaLift N := l.toMul.2
    let x : R.rawKernelOmegaLift N := ⟨q, hqOmega⟩
    obtain ⟨z, hz⟩ := (R.rawKernelOmegaEquiv N).surjective x
    have hzval :
        ((binaryCentralOmegaEmbedding z :
          (R.rawQuotientMap N).ker) :
            preE7PairAction s p ⧸ N.1) = q := by
      rw [← R.rawKernelOmegaEquiv_val N z]
      exact congrArg Subtype.val hz
    have hqOuter : q ∈ (R.outerQuotientMap N).ker := by
      rw [R.outerQuotientMap_ker_eq_zeroCutBase_ker N]
      exact (R.frame.zeroCutKernelMap N.1 l.toMul.1).property
    have hzker : z ∈ (R.rawKernelOmegaProjection N).ker := by
      apply MonoidHom.mem_ker.mpr
      apply Subtype.ext
      change R.outerQuotientMap N
        ((binaryCentralOmegaEmbedding z :
          (R.rawQuotientMap N).ker) :
            preE7PairAction s p ⧸ N.1) = 1
      rw [hzval]
      exact MonoidHom.mem_ker.mp hqOuter
    let zker : (R.rawKernelOmegaProjection N).ker := ⟨z, hzker⟩
    have hchart : R.rawKernelOmegaOuterInclusion N zker =
        R.outerZeroCutKernelEquivRawKernelProjectionKer N
          (R.frame.zeroCutMap N.1 l.toMul.1) := by
      apply Subtype.ext
      apply Subtype.ext
      exact hzval.trans
        (R.outerZeroCutKernelEquivRawKernelProjectionKer_val
          N l.toMul.1).symm
    have hcoord :=
      (congrArg (R.outerZeroCutKernelEquivRawKernelProjectionKer N).symm
        hchart).trans
        ((R.outerZeroCutKernelEquivRawKernelProjectionKer N).symm_apply_apply
          (R.frame.zeroCutMap N.1 l.toMul.1))
    refine ⟨Additive.ofMul zker, ?_⟩
    exact (R.rawKernelOmegaOuterCoordinateMap_apply N (Additive.ofMul zker)).trans
      ((congrArg Multiplicative.toAdd hcoord).trans
        (R.outerOmegaZeroCutMap_apply N l).symm)

theorem rawKernelProjection_ker_isPGroup
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    IsPGroup 2 (R.rawKernelProjection N).ker :=
  (R.outerQuotientMap_kernel_isPGroup N).of_equiv
    (R.outerKernelEquivRawKernelProjectionKer N)

theorem rawQuotientMap_surjective
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    Function.Surjective (R.rawQuotientMap N) :=
  (R.innerQuotientMap_surjective N).comp
    (R.outerQuotientMap_surjective N)

theorem rawQuotientMap_kernel_isPGroup
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    IsPGroup 2 (R.rawQuotientMap N).ker := by
  have hpreimage : IsPGroup 2
      ((R.innerQuotientMap N).ker.comap (R.outerQuotientMap N)) :=
    (R.innerQuotientMap_kernel_isPGroup N).comap_of_ker_isPGroup
      (R.outerQuotientMap N) (R.outerQuotientMap_kernel_isPGroup N)
  have hker : (R.rawQuotientMap N).ker =
      (R.innerQuotientMap N).ker.comap (R.outerQuotientMap N) := by
    ext q
    simp only [rawQuotientMap, MonoidHom.mem_ker, MonoidHom.comp_apply,
      Subgroup.mem_comap]
  rw [hker]
  exact hpreimage

/-- The catalogue-facing direct quotient map. -/
noncomputable def quotientMap
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    (preE7PairAction s p ⧸ N.1) →*
      (D.top ⧸ D.normalRegistry.state (R.topNormalState N)) :=
  (QuotientGroup.quotientMulEquivOfEq
      (R.topNormalState_spec N).symm).toMonoidHom.comp
    (R.rawQuotientMap N)

theorem quotientMap_surjective
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    Function.Surjective (R.quotientMap N) :=
  (QuotientGroup.quotientMulEquivOfEq
      (R.topNormalState_spec N).symm).surjective.comp
    (R.rawQuotientMap_surjective N)

theorem quotientMap_ker_eq_rawQuotientMap_ker
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    (R.quotientMap N).ker = (R.rawQuotientMap N).ker := by
  ext q
  simp only [quotientMap, MonoidHom.mem_ker, MonoidHom.comp_apply]
  change (QuotientGroup.quotientMulEquivOfEq (R.topNormalState_spec N).symm)
      (R.rawQuotientMap N q) = 1 ↔ R.rawQuotientMap N q = 1
  exact (QuotientGroup.quotientMulEquivOfEq
    (R.topNormalState_spec N).symm).map_eq_one_iff

/-- Both successive elementary pair kernels combine to the actual binary
direct-quartet kernel of the selected literal-top quotient. -/
theorem quotientMap_kernel_isPGroup
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    IsPGroup 2 (R.quotientMap N).ker := by
  rw [R.quotientMap_ker_eq_rawQuotientMap_ker N]
  exact R.rawQuotientMap_kernel_isPGroup N

end DegreeTwoPairTopTowerRealization
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
