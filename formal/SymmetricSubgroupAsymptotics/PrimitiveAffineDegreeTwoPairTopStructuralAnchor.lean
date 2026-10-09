import SymmetricSubgroupAsymptotics.BinaryPairZeroCutExtension
import SymmetricSubgroupAsymptotics.BinaryTransitiveCentralCriterion
import SymmetricSubgroupAsymptotics.FiniteNormalRegistryQuotientSocle
import SymmetricSubgroupAsymptotics.Non2SchurBound
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopBinaryKernelRows

/-!
# Structural binary-kernel anchors for pair-top rows

For an original normal subgroup `N`, the quotient of the original pair
action maps onto the corresponding quotient of the literal catalogue top.
Its kernel is the actual retained binary pair section.  This file constructs
that map, identifies its kernel with the zero-cut kernel, and bounds the
central binary rank by the dimension of the zero-cut module.

Consequently a quotient-socle tuple from the finite top-normal registry and
a dimension bound from the finite invariant-module registry give the actual
`DegreeTwoPairBinaryKernelAnchor` on the original quotient.  No character
labels indexed independently of the original normal remain in this bridge.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

namespace DegreeTwoPairTopRealization

variable {s : ℕ} {D : DegreeTwoPairTopFiniteInterface s}
  {p : PreE7PairActionClass s}
  (R : DegreeTwoPairTopRealization D p)

/-- The original quotient maps onto the literal catalogue-top quotient
selected by its actual top-normal state. -/
noncomputable def quotientMap
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    (preE7PairAction s p ⨸ N.1) →*
      (D.top ⨸ D.normalRegistry.state (R.topNormalState N)) := by
  letI : N.1.Normal := N.2
  let f : preE7PairAction s p →*
      D.top ⨸ D.normalRegistry.state (R.topNormalState N) :=
    (QuotientGroup.mk' (D.normalRegistry.state (R.topNormalState N))).comp
      (R.topEquiv.symm.toMonoidHom.comp R.frame.top.rangeRestrict)
  apply QuotientGroup.lift N.1 f
  intro u hu
  apply MonoidHom.mem_ker.mpr
  apply QuotientGroup.eq_one_iff.mpr
  rw [R.topNormalState_spec N]
  change R.topEquiv (R.topEquiv.symm (R.frame.top.rangeRestrict u)) ∈
    N.1.map R.frame.top.rangeRestrict
  rw [R.topEquiv.apply_symm_apply]
  exact ⟨u, hu, rfl⟩

@[simp] theorem quotientMap_apply
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal})
    (u : preE7PairAction s p) :
    R.quotientMap N (QuotientGroup.mk' N.1 u) =
      QuotientGroup.mk'
        (D.normalRegistry.state (R.topNormalState N))
        (R.topEquiv.symm (R.frame.top.rangeRestrict u)) :=
  rfl

theorem quotientMap_surjective
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    Function.Surjective (R.quotientMap N) := by
  letI : N.1.Normal := N.2
  intro q
  obtain ⟨d, rfl⟩ := QuotientGroup.mk'_surjective
    (D.normalRegistry.state (R.topNormalState N)) q
  obtain ⟨u, hu⟩ := R.frame.top.rangeRestrict_surjective
    (R.topEquiv d)
  refine ⟨QuotientGroup.mk' N.1 u, ?_⟩
  rw [R.quotientMap_apply N u, hu, R.topEquiv.symm_apply_apply]

private theorem catalogueTop_mem_state_iff
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal})
    (u : preE7PairAction s p) :
    R.topEquiv.symm (R.frame.top.rangeRestrict u) ∈
        D.normalRegistry.state (R.topNormalState N) ↔
      u ∈ R.frame.top.ker ⊔ N.1 := by
  rw [R.topNormalState_spec N]
  change R.topEquiv (R.topEquiv.symm (R.frame.top.rangeRestrict u)) ∈
      N.1.map R.frame.top.rangeRestrict ↔ _
  rw [R.topEquiv.apply_symm_apply]
  constructor
  · rintro ⟨n, hn, hnu⟩
    have hk : n⁻¹ * u ∈ R.frame.top.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hnu, inv_mul]
    have hn' : n ∈ R.frame.top.ker ⊔ N.1 :=
      Subgroup.mem_sup_right hn
    have hk' : n⁻¹ * u ∈ R.frame.top.ker ⊔ N.1 :=
      Subgroup.mem_sup_left hk
    have hmul := (R.frame.top.ker ⊔ N.1).mul_mem hn' hk'
    simpa using hmul
  · intro hu
    letI : N.1.Normal := N.2
    obtain ⟨k, hk, n, hn, hkn⟩ :=
      Subgroup.mem_sup_of_normal_right.mp hu
    refine ⟨n, hn, ?_⟩
    rw [← hkn, map_mul, MonoidHom.mem_ker.mp hk, one_mul]

/-- The catalogue-top quotient has exactly the same binary kernel as the
intrinsic zero-cut quotient of the original pair frame. -/
theorem quotientMap_ker_eq_zeroCutBase_ker
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    (R.quotientMap N).ker = (R.frame.zeroCutBase N.1).ker := by
  letI : N.1.Normal := N.2
  ext q
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective N.1 q
  simp only [MonoidHom.mem_ker, R.quotientMap_apply,
    BinaryPairFrame.zeroCutBase_apply, QuotientGroup.eq_one_iff]
  exact R.catalogueTop_mem_state_iff N u

/-- The kernel of the catalogue-top quotient is binary because it is the
actual zero-cut pair module. -/
theorem quotientMap_kernel_isPGroup
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    IsPGroup 2 (R.quotientMap N).ker := by
  letI : N.1.Normal := N.2
  rw [R.quotientMap_ker_eq_zeroCutBase_ker N]
  have hmodule : IsPGroup 2 (Multiplicative (R.frame.zeroCutModule N.1)) :=
    primeModule_isPGroup 2 (R.frame.zeroCutModule N.1)
  exact hmodule.of_equiv (R.frame.zeroCutKernelEquiv N.1)

/-- The central involution rank of the binary quotient kernel is no larger
than the full zero-cut module dimension. -/
theorem quotientMap_kernel_rank_le_zeroCutModule
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    Module.finrank (ZMod 2)
        (Additive (binaryCentralOmega (R.quotientMap N).ker)) ≤
      Module.finrank (ZMod 2) (R.frame.zeroCutModule N.1) := by
  letI : N.1.Normal := N.2
  have hcard : Nat.card (binaryCentralOmega (R.quotientMap N).ker) ≤
      Nat.card (R.quotientMap N).ker :=
    Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  have hkernelCard : Nat.card (R.quotientMap N).ker =
      2 ^ Module.finrank (ZMod 2) (R.frame.zeroCutModule N.1) := by
    rw [R.quotientMap_ker_eq_zeroCutBase_ker N]
    calc
      Nat.card (R.frame.zeroCutBase N.1).ker =
          Nat.card (Multiplicative (R.frame.zeroCutModule N.1)) :=
        (Nat.card_congr (R.frame.zeroCutKernelEquiv N.1).toEquiv).symm
      _ = Nat.card (R.frame.zeroCutModule N.1) :=
        Nat.card_congr Multiplicative.toAdd
      _ = 2 ^ Module.finrank (ZMod 2) (R.frame.zeroCutModule N.1) := by
        simpa only [Nat.card_zmod] using
          Module.natCard_eq_pow_finrank
            (K := ZMod 2) (V := R.frame.zeroCutModule N.1)
  rw [binaryCentralOmega_card_eq_pow_finrank, hkernelCard] at hcard
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hcard

end DegreeTwoPairTopRealization

/-! ## Finite registry assembly -/

/-- The two finite functions needed to build every actual original-quotient
anchor.  The top state carries a quotient-socle tuple; the module state
carries a bound for the actual zero-cut dimension selected by that normal.
-/
structure DegreeTwoPairTopStructuralAnchorData {s : ℕ}
    (D : DegreeTwoPairTopFiniteInterface s)
    (p : PreE7PairActionClass s)
    (R : DegreeTwoPairTopRealization D p) : Type 1 where
  ordinaryCount : D.normalRegistry.State → ℕ
  relativeCount : D.ModuleState → ℕ
  topSocleGenerator : ∀ i,
    SocleNormalGeneratorBound
      (D.top ⨸ D.normalRegistry.state i) (ordinaryCount i)
  zeroCutRank_le : ∀ N,
    Module.finrank (ZMod 2) (R.frame.zeroCutModule N.1) ≤
      relativeCount (R.moduleState N)

namespace DegreeTwoPairTopStructuralAnchorData

variable {s : ℕ} {D : DegreeTwoPairTopFiniteInterface s}
  {p : PreE7PairActionClass s}
  {R : DegreeTwoPairTopRealization D p}
  (A : DegreeTwoPairTopStructuralAnchorData D p R)

/-- Install a uniformly padded quotient-socle family and one uniform
zero-cut rank cap.  This is the form emitted by a literal pair-top row: all
top normal states use the same padded ordinary count, and all module states
fit the row's certified section cap. -/
noncomputable def ofUniformCounts
    (ordinary relative : ℕ)
    (top : D.normalRegistry.QuotientSocleGeneratorFamily ordinary)
    (zeroCutRank_le : ∀ N,
      Module.finrank (ZMod 2) (R.frame.zeroCutModule N.1) ≤ relative) :
    DegreeTwoPairTopStructuralAnchorData D p R where
  ordinaryCount := fun _ ↦ ordinary
  relativeCount := fun _ ↦ relative
  topSocleGenerator := fun i ↦ (top.data i).quotientSocleGenerator
  zeroCutRank_le := zeroCutRank_le

def profileOfState
    (i : D.normalRegistry.State) (j : D.ModuleState) :
    DegreeTwoPairRelativeProfile :=
  degreeTwoPairOrdinaryRelativeProfile
    (A.ordinaryCount i) (A.relativeCount j)

def profile
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    DegreeTwoPairRelativeProfile :=
  A.profileOfState (R.topNormalState N) (R.moduleState N)

/-- Assemble the literal original-quotient anchor from the two finite
registry entries selected semantically by `N`. -/
noncomputable def anchor
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    DegreeTwoPairBinaryKernelAnchor
      (preE7PairAction s p ⨸ N.1) (A.profile N) := by
  letI : N.1.Normal := N.2
  exact DegreeTwoPairBinaryKernelAnchor.ofSurjectiveBinaryKernel
      hZmud (R.quotientMap N) (R.quotientMap_surjective N)
      (A.topSocleGenerator (R.topNormalState N))
      (R.quotientMap_kernel_isPGroup N)
      ((R.quotientMap_kernel_rank_le_zeroCutModule N).trans
        (A.zeroCutRank_le N))

/-- If the finite profile table lies in the row's permitted menu, the
structural bridge produces the complete binary-kernel row data. -/
noncomputable def rowData
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (allowedProfiles : Finset DegreeTwoPairRelativeProfile)
    (allowed_capacity : ∀ profile ∈ allowedProfiles,
      profile.slope ≤ preE7CharacterWindow (2 * s))
    (profile_mem : ∀ N, A.profile N ∈ allowedProfiles) :
    DegreeTwoPairTopBinaryKernelRowData
      D allowedProfiles p R :=
  DegreeTwoPairTopBinaryKernelRowData.ofProfileTable
    allowedProfiles allowed_capacity A.profileOfState profile_mem
    (A.anchor hZmud)

end DegreeTwoPairTopStructuralAnchorData

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
