import SymmetricSubgroupAsymptotics.BinaryPairZeroCutExtension
import SymmetricSubgroupAsymptotics.BinaryPairSectionSchurCapacity
import SymmetricSubgroupAsymptotics.BinaryInvariantCyclicGeneratorBound
import SymmetricSubgroupAsymptotics.BinaryTransitiveCentralCriterion
import SymmetricSubgroupAsymptotics.FiniteSurjectiveKernelTransport
import SymmetricSubgroupAsymptotics.FiniteNormalRegistryQuotientSocle
import SymmetricSubgroupAsymptotics.Non2SchurBound
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopBinaryKernelRows
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairSchurLift
import SymmetricSubgroupAsymptotics.PermutationFunctionSelfDual

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

namespace BinaryPairFrame

variable {X : Type} {s : ℕ} {U : Subgroup (Equiv.Perm X)}
  (F : BinaryPairFrame U (Fin s))

/-- The intrinsic normal space and the ambient registry axis are the same
subspace after including the pair kernel in the full coordinate module. -/
theorem normalSpace_map_subtype_eq_ambientAxis (N : Subgroup U) :
    (F.normalSpace N).map F.kernelSpace.subtype = F.ambientAxis N := by
  ext v
  constructor
  · rintro ⟨m, hm, rfl⟩
    obtain ⟨k, hk⟩ := hm
    refine (F.mem_ambientAxis N _).2
      ⟨k.toMul.val, k.toMul.property, ?_⟩
    exact congrArg Subtype.val hk
  · intro hv
    obtain ⟨k, hk, hkv⟩ := (F.mem_ambientAxis N v).1 hv
    let m : F.kernelSpace := (F.kernelSpaceHom k).toAdd
    refine ⟨m, ?_, ?_⟩
    · exact ⟨Additive.ofMul (⟨k, hk⟩ : N.subgroupOf F.top.ker), rfl⟩
    · exact hkv

theorem normalSpace_finrank_eq_ambientAxis (N : Subgroup U) :
    Module.finrank (ZMod 2) (F.normalSpace N) =
      Module.finrank (ZMod 2) (F.ambientAxis N) := by
  have h := (Submodule.equivMapOfInjective F.kernelSpace.subtype
    Subtype.val_injective (F.normalSpace N)).finrank_eq
  rw [F.normalSpace_map_subtype_eq_ambientAxis N] at h
  exact h

theorem ambientAxis_top :
    F.ambientAxis (⊤ : Subgroup U) = F.kernelSpace := by
  apply le_antisymm (F.ambientAxis_le_kernelSpace ⊤)
  intro v hv
  obtain ⟨k, rfl⟩ := hv
  exact (F.mem_ambientAxis ⊤ (F.bits k.toMul)).2
    ⟨k.toMul, Subgroup.mem_top, rfl⟩

end BinaryPairFrame

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

/-- The intrinsic acting quotient and the literal catalogue-top quotient
are canonically equivalent because the two onto maps from the original
quotient have the same kernel. -/
noncomputable def zeroCutBaseEquivCatalogueTop
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    (preE7PairAction s p ⨸ (R.frame.top.ker ⊔ N.1)) ≃*
      (D.top ⨸ D.normalRegistry.state (R.topNormalState N)) := by
  letI : N.1.Normal := N.2
  exact surjectiveTargetEquivOfKernelEq
    (R.frame.zeroCutBase N.1) (R.quotientMap N)
    (R.frame.zeroCutBase_surjective N.1) (R.quotientMap_surjective N)
    (R.quotientMap_ker_eq_zeroCutBase_ker N).symm

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

/-- The two module states selected by `N` and by the top original normal
recover the exact dimension of the retained zero-cut section.  This turns
finite module-state dimensions into the rank bounds consumed by the anchor
constructor. -/
theorem zeroCutModule_finrank_add_moduleState
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    Module.finrank (ZMod 2) (R.frame.zeroCutModule N.1) +
        Module.finrank (ZMod 2) (D.moduleState (R.moduleState N)) =
      Module.finrank (ZMod 2)
        (D.moduleState
          (R.moduleState
            (⟨⊤, inferInstance⟩ :
              {M : Subgroup (preE7PairAction s p) // M.Normal}))) := by
  letI : N.1.Normal := N.2
  let topAxis : {M : Subgroup (preE7PairAction s p) // M.Normal} :=
    ⟨⊤, inferInstance⟩
  have hquot := (R.frame.normalSpace N.1).finrank_quotient_add_finrank
  have hnormal := R.frame.normalSpace_finrank_eq_ambientAxis N.1
  have hstateN := congrArg
    (fun W : Subrepresentation
        (permutationFunctionRepresentation (ZMod 2) D.top (Fin s)) ↦
      Module.finrank (ZMod 2) W)
    (R.moduleState_spec N)
  have hstateTop := congrArg
    (fun W : Subrepresentation
        (permutationFunctionRepresentation (ZMod 2) D.top (Fin s)) ↦
      Module.finrank (ZMod 2) W)
    (R.moduleState_spec topAxis)
  change Module.finrank (ZMod 2)
      (R.frame.kernelSpace ⨸ R.frame.normalSpace N.1) +
      Module.finrank (ZMod 2) (R.frame.normalSpace N.1) =
        Module.finrank (ZMod 2) R.frame.kernelSpace at hquot
  change Module.finrank (ZMod 2) (D.moduleState (R.moduleState N)) =
    Module.finrank (ZMod 2) (R.frame.ambientAxis N.1) at hstateN
  change Module.finrank (ZMod 2) (D.moduleState (R.moduleState topAxis)) =
    Module.finrank (ZMod 2) (R.frame.ambientAxis (⊤ :
      Subgroup (preE7PairAction s p))) at hstateTop
  rw [BinaryPairFrame.zeroCutModule, hstateN, ← hnormal,
    show (⟨⊤, inferInstance⟩ :
      {M : Subgroup (preE7PairAction s p) // M.Normal}) = topAxis from rfl,
    hstateTop, R.frame.ambientAxis_top]
  exact hquot

theorem moduleState_le_topModuleState
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    D.moduleState (R.moduleState N) ≤
      D.moduleState
        (R.moduleState
          (⟨⊤, inferInstance⟩ :
            {M : Subgroup (preE7PairAction s p) // M.Normal})) := by
  let topAxis : {M : Subgroup (preE7PairAction s p) // M.Normal} :=
    ⟨⊤, inferInstance⟩
  rw [R.moduleState_spec N,
    show (⟨⊤, inferInstance⟩ :
      {M : Subgroup (preE7PairAction s p) // M.Normal}) = topAxis from rfl,
    R.moduleState_spec topAxis]
  change R.frame.ambientAxis N.1 ≤
    R.frame.ambientAxis (⊤ : Subgroup (preE7PairAction s p))
  rw [R.frame.ambientAxis_top]
  exact R.frame.ambientAxis_le_kernelSpace N.1

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

/-- Finite-state form of `ofUniformCounts`.  The section cap is checked only
on module states contained in the actual kernel-module state.  The generic
dimension identity above then proves the required bound for every original
normal subgroup. -/
noncomputable def ofFiniteStateBounds
    (ordinary relative : ℕ)
    (top : D.normalRegistry.QuotientSocleGeneratorFamily ordinary)
    (sectionRank_le : ∀ j,
      D.moduleState j ≤
          D.moduleState
            (R.moduleState
              (⟨⊤, inferInstance⟩ :
                {M : Subgroup (preE7PairAction s p) // M.Normal})) →
        Module.finrank (ZMod 2)
            (D.moduleState
              (R.moduleState
                (⟨⊤, inferInstance⟩ :
                  {M : Subgroup (preE7PairAction s p) // M.Normal}))) ≤
          Module.finrank (ZMod 2) (D.moduleState j) + relative) :
    DegreeTwoPairTopStructuralAnchorData D p R :=
  ofUniformCounts ordinary relative top (fun N ↦ by
    have hsum := R.zeroCutModule_finrank_add_moduleState N
    have hbound := sectionRank_le (R.moduleState N)
      (R.moduleState_le_topModuleState N)
    omega)

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

/-! ## Schur-capacity assembly -/

/-- The finite data actually measured by `pair_top_modules.jsonl.gz`.
The top-normal registry supplies a uniformly padded socle tuple.  The
module table supplies a uniform generator bound on the dual natural
permutation module; the subquotient theorem turns it into a Schur-capacity
bound for every retained pair section.

Unlike `DegreeTwoPairTopStructuralAnchorData`, this structure does not
bound the dimension of the full binary kernel. -/
structure DegreeTwoPairTopSchurData {s : ℕ}
    (D : DegreeTwoPairTopFiniteInterface s)
    (p : PreE7PairActionClass s)
    (R : DegreeTwoPairTopRealization D p) : Type 1 where
  ordinary : ℕ
  relative : ℕ
  top : D.normalRegistry.QuotientSocleGeneratorFamily ordinary
  dualUniform : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) D.top (Fin s)).dual
      relative

namespace DegreeTwoPairTopSchurData

/-- Assemble the Schur row directly from the two checked finite registries:
quotient-socle generators on the normal axis and cyclic module generators on
the invariant-state axis. -/
noncomputable def ofFiniteGenerators {s : ℕ}
    {D : DegreeTwoPairTopFiniteInterface s}
    {p : PreE7PairActionClass s}
    {R : DegreeTwoPairTopRealization D p}
    (ordinary relative : ℕ)
    (top : D.normalRegistry.QuotientSocleGeneratorFamily ordinary)
    (moduleGenerators :
      BinaryInvariantCyclicGeneratorBound D.moduleRegistry relative) :
    DegreeTwoPairTopSchurData D p R where
  ordinary := ordinary
  relative := relative
  top := top
  dualUniform := permutationFunctionRepresentation_dual_uniform
    moduleGenerators.uniform

variable {s : ℕ} {D : DegreeTwoPairTopFiniteInterface s}
  {p : PreE7PairActionClass s}
  {R : DegreeTwoPairTopRealization D p}
  (A : DegreeTwoPairTopSchurData D p R)

def profile : DegreeTwoPairRelativeProfile :=
  degreeTwoPairOrdinaryRelativeProfile A.ordinary A.relative

/-- The literal top quotient selected by an original normal has the
ordinary envelope supplied by its checked finite socle certificate. -/
noncomputable def literalTopEnvelope
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    DegreeTwoPairRelativeQuotientEnvelope
      (D.top ⨸ D.normalRegistry.state (R.topNormalState N))
      (degreeTwoPairGeneralProfile A.ordinary) :=
  (DegreeTwoPairBinaryKernelAnchor.ofSocleGeneratorBound hZmud
    (A.top.data (R.topNormalState N)).quotientSocleGenerator).toQuotientEnvelope lit

/-- Complete Schur lift on one literal original-normal axis.  The top
coefficient is transported across the canonical same-kernel equivalence;
the extension representation and its chart remain the actual objects from
the original pair frame. -/
noncomputable def envelope
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    DegreeTwoPairRelativeQuotientEnvelope
      (preE7PairAction s p ⨸ N.1) A.profile := by
  letI : N.1.Normal := N.2
  let top := (A.literalTopEnvelope hZmud lit N).ofTargetEquiv
    (R.zeroCutBaseEquivCatalogueTop N)
  exact degreeTwoPairSchurLiftEnvelope
    (R.frame.zeroCutBase N.1) (R.frame.zeroCutBase_surjective N.1)
    (Rep.of (R.frame.sectionRepresentation N.1))
    (R.frame.sectionModuleChart N.1)
    A.ordinary A.relative top
    (R.frame.sectionRepresentation_schurCapacity_le_of_uniformDualEquiv
      (permutationFunctionRepresentation (ZMod 2) D.top (Fin s))
      R.topEquiv R.module_action_eq A.relative A.dualUniform N.1)

/-- Universal all-original-normal lift data for the row. -/
noncomputable def liftData
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    (capacity : A.profile.slope ≤ preE7CharacterWindow (2 * s)) :
    DegreeTwoPairRelativeLiftData s p where
  profile := fun _ ↦ A.profile
  capacity := fun _ ↦ capacity
  envelope := A.envelope hZmud lit

/-- Package the Schur row in the catalogue-facing conclusion type. -/
noncomputable def liftConclusion
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    (allowedProfiles : Finset DegreeTwoPairRelativeProfile)
    (allowed_capacity : ∀ profile ∈ allowedProfiles,
      profile.slope ≤ preE7CharacterWindow (2 * s))
    (profile_mem : A.profile ∈ allowedProfiles) :
    DegreeTwoPairTopRelativeLiftConclusion D p :=
  { lift := A.liftData hZmud lit (allowed_capacity A.profile profile_mem)
    topNormalState := R.topNormalState
    moduleState := R.moduleState
    profileOfState := fun _ _ ↦ A.profile
    profile_eq := fun _ ↦ rfl
    allowedProfiles := allowedProfiles
    allowed_capacity := allowed_capacity
    profile_mem := fun _ ↦ profile_mem }

end DegreeTwoPairTopSchurData

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
