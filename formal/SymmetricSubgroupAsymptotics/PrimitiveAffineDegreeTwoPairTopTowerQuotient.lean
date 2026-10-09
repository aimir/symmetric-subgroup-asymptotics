import SymmetricSubgroupAsymptotics.BinaryPairLiteralTopQuotient
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopOriginalNormalSignature

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

variable {s t : ℕ} {D : DegreeTwoPairTopFiniteInterface t}
  {p : PreE7PairActionClass s}
  (R : DegreeTwoPairTopTowerRealization D p)

/-- The first pair quotient, with the actual image of `N` as denominator. -/
noncomputable def outerQuotientMap
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    (preE7PairAction s p ⫽ N.1) →*
      (R.frame.top.range ⫽ R.outerTopNormal N.1) := by
  letI : N.1.Normal := N.2
  let f : preE7PairAction s p →*
      (R.frame.top.range ⫽ R.outerTopNormal N.1) :=
    (QuotientGroup.mk' (R.outerTopNormal N.1)).comp
      R.frame.top.rangeRestrict
  apply QuotientGroup.lift N.1 f
  intro u hu
  apply MonoidHom.mem_ker.mpr
  apply QuotientGroup.eq_one_iff.mpr
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
      rw [MonoidHom.mem_ker, map_mul, map_inv, hnu, inv_mul]
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
    rw [← hkn, map_mul, MonoidHom.mem_ker.mp hk, one_mul]

theorem outerQuotientMap_ker_eq_zeroCutBase_ker
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    (R.outerQuotientMap N).ker = (R.frame.zeroCutBase N.1).ker := by
  letI : N.1.Normal := N.2
  ext q
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective N.1 q
  simp only [MonoidHom.mem_ker, R.outerQuotientMap_apply,
    R.frame.zeroCutBase_apply, QuotientGroup.eq_one_iff]
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
    (R.frame.top.range ⫽ R.outerTopNormal N.1) →*
      (D.top ⫽ R.topNormal N.1) := by
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

/-- The direct map through both pair quotients before replacing the selected
normal by its equal finite-registry state. -/
noncomputable def rawQuotientMap
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    (preE7PairAction s p ⫽ N.1) →* (D.top ⫽ R.topNormal N.1) :=
  (R.innerQuotientMap N).comp (R.outerQuotientMap N)

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
    (preE7PairAction s p ⫽ N.1) →*
      (D.top ⫽ D.normalRegistry.state (R.topNormalState N)) :=
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
  simp only [quotientMap, MonoidHom.mem_ker, MonoidHom.comp_apply,
    map_eq_one_iff]

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
