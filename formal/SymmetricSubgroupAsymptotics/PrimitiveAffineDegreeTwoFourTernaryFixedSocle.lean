import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoFourTernaryBlocks
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeNineSocleGenerators
import SymmetricSubgroupAsymptotics.BinaryPairSubgroupCuts
import SymmetricSubgroupAsymptotics.PermutationBinaryTrivialSection
import SymmetricSubgroupAsymptotics.FiniteSurjectiveKernelTransport
import Mathlib.RepresentationTheory.Maschke

/-!
# The fixed socle in the four-ternary pair rows

This file isolates the fixed half of the socle estimate from the active
four-plane argument.  The normal cut is the literal retained pair kernel.
Its intersection with the fixed socle is read in the exact correlated pair
section, while the quotient is carried by the literal degree-twelve top.

There are two genuinely representation-theoretic leaves:

* the fixed pair section is a trivial section of the permutation module on
  the four actual ternary blocks, and hence has binary dimension at most two;
* the normal top image of the fixed part is disjoint from the displayed
  ternary core.

Everything after those two leaves is the formal normal-generation
filtration `2 + 1 = 3`.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoFourTernaryTopStructure

variable {D : DegreeTwoPairTopFiniteInterface 12}
  (S : DegreeTwoFourTernaryTopStructure D)

noncomputable local instance : S.core.Normal := S.core_normal

private abbrev LiteralNormalAxis
    {p : PreE7PairActionClass 12} :=
  {N : Subgroup (preE7PairAction 12 p) // N.Normal}

/-! ## The literal retained pair kernel -/

/-- Image of the actual correlated pair kernel in an original normal
quotient. -/
def retainedPairKernel
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p)
    (N : LiteralNormalAxis (p := p)) :
    Subgroup (preE7PairAction 12 p ⧸ N.1) := by
  let _S := S
  exact R.frame.top.ker.map (QuotientGroup.mk' N.1)

noncomputable instance retainedPairKernel_normal
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p)
    (N : LiteralNormalAxis (p := p)) :
    (S.retainedPairKernel R N).Normal :=
  Subgroup.Normal.map inferInstance (QuotientGroup.mk' N.1)
    (QuotientGroup.mk'_surjective N.1)

/-- The physical four-plane subgroup is contained in the physical pair
kernel before and after passage to the retained quotient. -/
theorem retainedAveragingImage_le_retainedPairKernel
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p)
    (N : LiteralNormalAxis (p := p)) :
    S.retainedAveragingImage R N ≤ S.retainedPairKernel R N := by
  exact Subgroup.map_mono
    (R.frame.coordinateSubgroup_le_kernel
      (S.averagingCoordinateRepresentation R).toSubmodule)

/-- The pair kernel has trivial literal top and therefore lies over the
displayed ternary core. -/
theorem retainedPairKernel_le_retainedTernaryImage
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p)
    (N : LiteralNormalAxis (p := p)) :
    S.retainedPairKernel R N ≤ S.retainedTernaryImage R N := by
  apply Subgroup.map_mono
  intro k hk
  change S.realizedTop R k ∈ S.core
  have htop : R.frame.top.rangeRestrict k = 1 := by
    apply Subtype.ext
    exact hk
  change R.topEquiv.symm (R.frame.top.rangeRestrict k) ∈ S.core
  rw [htop, map_one]
  exact Subgroup.one_mem S.core

/-- The fixed socle part used throughout the rest of the file. -/
abbrev retainedFixedSoclePart
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p)
    (N : LiteralNormalAxis (p := p)) :
    Subgroup (preE7PairAction 12 p ⧸ N.1) :=
  trivialActionSoclePart (preE7PairAction 12 p ⧸ N.1)
    (S.retainedTernaryImage R N)

/-! ## The common odd-core descent -/

/-- Every subgroup of the displayed ternary core is a three-group.  The
pointwise exponent hypothesis is enough here; no cardinality computation of
the core is needed. -/
theorem coreSubgroup_isPGroup_three
    (K : Subgroup D.top) (hKC : K ≤ S.core) : IsPGroup 3 K := by
  intro k
  refine ⟨1, ?_⟩
  apply Subtype.ext
  simpa only [pow_one] using
    congrArg Subtype.val (S.core_exponent_three ⟨k.1, hKC k.2⟩)

/-- A nonzero top-normal subgroup inside the displayed core has the same
three-point orbits as the whole core. -/
theorem normalCoreSubgroup_orbit_eq
    (K : Subgroup D.top) [K.Normal]
    (hKC : K ≤ S.core) (hK : K ≠ ⊥) (x : Fin 12) :
    MulAction.orbit K x = MulAction.orbit S.core x := by
  letI : MulAction.IsPretransitive D.top (Fin 12) := S.top_transitive
  have hsub : MulAction.orbit K x ⊆ MulAction.orbit S.core x := by
    rintro y ⟨k, rfl⟩
    exact ⟨⟨k.1, hKC k.2⟩, rfl⟩
  have hCcard : (MulAction.orbit S.core x).ncard = 3 := by
    let o : S.OrbitBlocks := Quotient.mk'' x
    have ho := S.orbit_card_eq_three o
    simpa only [o, MulAction.orbitRel.Quotient.orbit_mk,
      Nat.card_coe_set_eq] using ho
  have hKthree : IsPGroup 3 K := S.coreSubgroup_isPGroup_three K hKC
  obtain ⟨a, ha⟩ := hKthree.card_orbit x
  have hKcard : (MulAction.orbit K x).ncard = 3 := by
    have hle : 3 ^ a ≤ 3 := by
      rw [← ha, ← hCcard]
      exact Set.ncard_le_ncard hsub (by toFinite_tac)
    have hne : 3 ^ a ≠ 1 := by
      intro hone
      apply normal_orbit_card_ne_one_of_ne_bot K hK x
      simpa only [Nat.card_coe_set_eq, ha] using hone
    have haone : a = 1 := by
      rcases a with _ | a
      · exact (hne (by simp)).elim
      · rcases a with _ | a
        · rfl
        · have : 9 ≤ 3 ^ (Nat.succ (Nat.succ a)) := by
            have haPow : 1 ≤ 3 ^ a := Nat.one_le_pow a 3 (by norm_num)
            simp only [pow_succ]
            nlinarith
          omega
    simpa only [haone, pow_one] using ha
  apply Set.eq_of_subset_of_ncard_le hsub
  rw [hCcard, hKcard]

/-- No nonzero vector in the four ternary augmentation planes is fixed by
a nonzero top-normal subgroup of the displayed core. -/
theorem augmentationPlanes_fixed_eq_zero_of_normalCoreSubgroup
    (K : Subgroup D.top) [K.Normal]
    (hKC : K ≤ S.core) (hK : K ≠ ⊥)
    (v : S.augmentationPlanes)
    (hv : ∀ k : K,
      permutationFunctionRepresentation (ZMod 2) D.top (Fin 12) k.1 v.1 =
        v.1) :
    v = 0 := by
  letI : MulAction.IsPretransitive D.top (Fin 12) := S.top_transitive
  apply Subtype.ext
  funext x
  let o : S.OrbitBlocks := Quotient.mk'' x
  let B : S.Blocks := ⟨MulAction.orbit S.core x, by
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq D.top (0 : Fin 12) x
    refine ⟨g, ?_⟩
    change g • (MulAction.orbit S.core (0 : Fin 12) : Set (Fin 12)) =
      MulAction.orbit S.core x
    rw [MulAction.smul_orbit_eq_orbit_smul, hg]⟩
  have hB : (B.1 : Set (Fin 12)) = MulAction.orbit S.core x := rfl
  have hconst : ∀ y : B.1, v.1 y.1 = v.1 x := by
    intro y
    have hyC : y.1 ∈ MulAction.orbit S.core x := by
      rw [← hB]
      exact y.2
    rw [← S.normalCoreSubgroup_orbit_eq K hKC hK x] at hyC
    obtain ⟨k, hk⟩ := hyC
    have hfix := congrFun (hv k⁻¹) x
    simp only [permutationFunctionRepresentation_apply, Subgroup.coe_inv]
      at hfix
    rw [← hk]
    simpa only [inv_inv] using hfix
  have hsum := (S.mem_augmentationPlanes v.1).1 v.2 B
  have hcard : Nat.card B.1 = 3 := by
    have ho := S.orbit_card_eq_three o
    simpa only [B, o, MulAction.orbitRel.Quotient.orbit_mk] using ho
  have hsumConst : (∑ y : B.1, v.1 y.1) = v.1 x := by
    simp_rw [hconst]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_eq_nat_card,
      hcard]
    have htwo : ∀ z : ZMod 2, 2 • z = 0 := by decide
    rw [show (3 : ℕ) = 2 + 1 by norm_num, add_nsmul, htwo,
      zero_add, one_nsmul]
  rw [hsumConst] at hsum
  simpa only [Pi.zero_apply] using hsum

/-- Restriction of the four augmentation planes to one subgroup of the
displayed ternary core. -/
def augmentationNormalCoreRepresentation (K : Subgroup D.top) :
    Representation (ZMod 2) K S.augmentationPlanes :=
  (S.augmentationRepresentation).toRepresentation.comp K.subtype

theorem augmentationNormalCoreRepresentation_invariants_eq_bot
    (K : Subgroup D.top) [K.Normal]
    (hKC : K ≤ S.core) (hK : K ≠ ⊥) :
    (S.augmentationNormalCoreRepresentation K).invariants = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro v hv
  rw [Submodule.mem_bot]
  apply S.augmentationPlanes_fixed_eq_zero_of_normalCoreSubgroup K hKC hK v
  intro k
  exact congrArg Subtype.val (hv k)

/-- Maschke descent for the common four-plane module.  Since every
nonzero top-normal subgroup in the ternary core has odd order, a vector
fixed modulo an invariant cut has a fixed representative in an invariant
complement.  The preceding zero-invariants theorem then forces that
representative to vanish. -/
theorem augmentationPlanes_no_fixed_vector_mod_normalCoreSubgroup
    (K : Subgroup D.top) [K.Normal]
    (hKC : K ≤ S.core) (hK : K ≠ ⊥)
    (I : Subrepresentation (S.augmentationNormalCoreRepresentation K))
    (v : S.augmentationPlanes)
    (hv : v ∉ I.toSubmodule)
    (hfixedMod : ∀ k : K,
      S.augmentationNormalCoreRepresentation K k v - v ∈ I.toSubmodule) :
    False := by
  let ρ := S.augmentationNormalCoreRepresentation K
  have hKthree : IsPGroup 3 K := S.coreSubgroup_isPGroup_three K hKC
  obtain ⟨a, hcard⟩ := IsPGroup.iff_card.mp hKthree
  letI : NeZero (Nat.card K : ZMod 2) := by
    constructor
    intro hzero
    have hdiv : 2 ∣ Nat.card K := (ZMod.natCast_eq_zero_iff _ _).mp hzero
    rw [hcard] at hdiv
    have : 2 ∣ 3 := Nat.prime_two.dvd_of_dvd_pow hdiv
    norm_num at this
  obtain ⟨J, hIJ⟩ := exists_isCompl I
  have hvSup : v ∈ I.toSubmodule ⊔ J.toSubmodule := by
    have hvTop : v ∈ (⊤ : Subrepresentation ρ) := Submodule.mem_top
    rw [← hIJ.codisjoint.eq_top] at hvTop
    exact hvTop
  obtain ⟨i, hi, j, hj, hij⟩ := Submodule.mem_sup.mp hvSup
  have hjne : j ≠ 0 := by
    intro hjzero
    subst j
    simp only [add_zero] at hij
    apply hv
    rw [← hij]
    exact hi
  have hjfixed : j ∈ Representation.invariants ρ := by
    intro k
    have htotal : ρ k v - v ∈ I := hfixedMod k
    have hiDiff : ρ k i - i ∈ I :=
      I.toSubmodule.sub_mem (I.apply_mem_toSubmodule k hi) hi
    have hjDiffI : ρ k j - j ∈ I := by
      have heq : ρ k j - j = (ρ k v - v) - (ρ k i - i) := by
        rw [← hij, map_add]
        simp only [sub_eq_add_neg, neg_smul, one_smul]
        abel
      rw [heq]
      exact I.toSubmodule.sub_mem htotal hiDiff
    have hjDiffJ : ρ k j - j ∈ J :=
      J.toSubmodule.sub_mem (J.apply_mem_toSubmodule k hj) hj
    have hInf : ρ k j - j ∈ (I ⊓ J : Subrepresentation ρ) :=
      ⟨hjDiffI, hjDiffJ⟩
    have hbot : ρ k j - j ∈ (⊥ : Submodule (ZMod 2) S.augmentationPlanes) := by
      rw [hIJ.disjoint.eq_bot] at hInf
      exact hInf
    exact sub_eq_zero.mp (by simpa only [Submodule.mem_bot] using hbot)
  have hjzero : j = 0 := by
    have hjbot : j ∈ (⊥ : Submodule (ZMod 2) S.augmentationPlanes) := by
      rw [← S.augmentationNormalCoreRepresentation_invariants_eq_bot
        K hKC hK]
      exact hjfixed
    simpa only [Submodule.mem_bot] using hjbot
  exact hjne hjzero

/-! ## Exact coordinates on the fixed pair section -/

/-- The intrinsic quotient subspace, included into the ambient coordinate
module, is the literal axis cut out by the original normal subgroup.  This
narrow local form keeps the fixed-socle module independent of the catalogue
anchor import chain. -/
private theorem normalSpace_map_subtype_eq_ambientAxis
    {X : Type} {s : ℕ} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin s)) (N : Subgroup U) :
    (F.normalSpace N).map F.kernelSpace.subtype = F.ambientAxis N := by
  ext v
  constructor
  · rintro ⟨m, hm, rfl⟩
    obtain ⟨k, hk⟩ := hm
    refine (F.mem_ambientAxis N _).2 ⟨k.toMul.val, k.toMul.property, ?_⟩
    exact congrArg Subtype.val hk
  · intro hv
    obtain ⟨k, hk, hkv⟩ := (F.mem_ambientAxis N v).1 hv
    let m : F.kernelSpace := (F.kernelSpaceHom k).toAdd
    refine ⟨m, ?_, ?_⟩
    · exact ⟨Additive.ofMul (⟨k, hk⟩ : N.subgroupOf F.top.ker), rfl⟩
    · exact hkv

/-- The full inverse image of the fixed socle, restricted to the literal
pair kernel.  It contains the original normal intersection with that
kernel, so `sectionSubgroupImage` gives its exact quotient coordinates. -/
def fixedPairPreimage
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p)
    (N : LiteralNormalAxis (p := p)) :
    Subgroup R.frame.top.ker :=
  ((S.retainedFixedSoclePart R N).comap
    (QuotientGroup.mk' N.1)).subgroupOf R.frame.top.ker

theorem normalSubgroupOfPairKernel_le_fixedPairPreimage
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p)
    (N : LiteralNormalAxis (p := p)) :
    N.1.subgroupOf R.frame.top.ker ≤ S.fixedPairPreimage R N := by
  intro k hk
  change QuotientGroup.mk' N.1 (k.1 : preE7PairAction 12 p) ∈
    S.retainedFixedSoclePart R N
  have hq : QuotientGroup.mk' N.1 (k.1 : preE7PairAction 12 p) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hk
  rw [hq]
  exact Subgroup.one_mem _

/-- Literal vector space of the fixed pair-kernel section.  It is the image
of the exact subgroup above under the canonical correlated-kernel quotient
map; no full-coordinate-product replacement is made. -/
def fixedPairSpace
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p)
    (N : LiteralNormalAxis (p := p)) :
    Submodule (ZMod 2)
      (R.frame.kernelSpace ⧸ R.frame.normalSpace N.1) :=
  sectionSubgroupImage (p := 2) (R.frame.sectionMap N.1)
    (S.fixedPairPreimage R N)

/-- The quotient of the fixed pair preimage realized inside the retained
quotient. -/
def fixedPairIntersectionMap
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p)
    (N : LiteralNormalAxis (p := p)) :
    S.fixedPairPreimage R N →*
      ((S.retainedFixedSoclePart R N ⊓ S.retainedPairKernel R N) :
        Subgroup (preE7PairAction 12 p ⧸ N.1)) where
  toFun k := ⟨QuotientGroup.mk' N.1 (k.1 : preE7PairAction 12 p),
    k.2, ⟨k.1, k.1.2, rfl⟩⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (QuotientGroup.mk' N.1)
  map_mul' k l := by
    apply Subtype.ext
    exact map_mul (QuotientGroup.mk' N.1) (k.1 : preE7PairAction 12 p) l.1

theorem fixedPairIntersectionMap_surjective
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p)
    (N : LiteralNormalAxis (p := p)) :
    Function.Surjective (S.fixedPairIntersectionMap R N) := by
  rintro ⟨x, hxH, hxE⟩
  obtain ⟨k, hk, rfl⟩ := hxE
  let kK : R.frame.top.ker := ⟨k, hk⟩
  have hkL : kK ∈ S.fixedPairPreimage R N := hxH
  exact ⟨⟨kK, hkL⟩, rfl⟩

/-- The same quotient of the fixed pair preimage realized in its exact
binary vector coordinates. -/
def fixedPairSpaceMap
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p)
    (N : LiteralNormalAxis (p := p)) :
    S.fixedPairPreimage R N →* Multiplicative (S.fixedPairSpace R N) where
  toFun k := Multiplicative.ofAdd
    ⟨(R.frame.sectionMap N.1 k.1).toAdd,
      (sectionSubgroupImage_mem_iff (p := 2)
        (R.frame.sectionMap N.1) (S.fixedPairPreimage R N)
        (by
          rw [R.frame.sectionMap_ker]
          exact S.normalSubgroupOfPairKernel_le_fixedPairPreimage R N)
        k.1).2 k.2⟩
  map_one' := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd (map_one (R.frame.sectionMap N.1))
  map_mul' k l := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd
      (map_mul (R.frame.sectionMap N.1) k.1 l.1)

theorem fixedPairSpaceMap_surjective
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p)
    (N : LiteralNormalAxis (p := p)) :
    Function.Surjective (S.fixedPairSpaceMap R N) := by
  intro v
  obtain ⟨k, hk⟩ := R.frame.sectionMap_surjective N.1
    (Multiplicative.ofAdd v.1)
  have hkL : k ∈ S.fixedPairPreimage R N :=
    (sectionSubgroupImage_mem_iff (p := 2)
      (R.frame.sectionMap N.1) (S.fixedPairPreimage R N)
      (by
        rw [R.frame.sectionMap_ker]
        exact S.normalSubgroupOfPairKernel_le_fixedPairPreimage R N)
      k).1 (by
        rw [hk]
        exact v.2)
  refine ⟨⟨k, hkL⟩, ?_⟩
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  exact congrArg Multiplicative.toAdd hk

theorem fixedPairIntersectionMap_ker_eq_fixedPairSpaceMap_ker
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p)
    (N : LiteralNormalAxis (p := p)) :
    (S.fixedPairIntersectionMap R N).ker =
      (S.fixedPairSpaceMap R N).ker := by
  ext k
  constructor
  · intro hk
    have hq : QuotientGroup.mk' N.1 (k.1 : preE7PairAction 12 p) = 1 :=
      congrArg Subtype.val (MonoidHom.mem_ker.mp hk)
    have hs : R.frame.sectionMap N.1 k.1 = 1 := by
      apply MonoidHom.mem_ker.mp
      rw [R.frame.sectionMap_ker]
      exact (QuotientGroup.eq_one_iff
        (k.1 : preE7PairAction 12 p)).mp hq
    apply MonoidHom.mem_ker.mpr
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd hs
  · intro hk
    have hsAdd := congrArg
      (fun z : Multiplicative (S.fixedPairSpace R N) ↦ z.toAdd.1)
      (MonoidHom.mem_ker.mp hk)
    have hs : R.frame.sectionMap N.1 k.1 = 1 := by
      apply Multiplicative.toAdd.injective
      exact hsAdd
    have hkN : k.1 ∈ N.1.subgroupOf R.frame.top.ker := by
      rw [← R.frame.sectionMap_ker]
      exact MonoidHom.mem_ker.mpr hs
    apply MonoidHom.mem_ker.mpr
    apply Subtype.ext
    exact (QuotientGroup.eq_one_iff
      (k.1 : preE7PairAction 12 p)).mpr hkN

/-- Exact cardinal transport through `BinaryPairFrame.sectionMap`.  Both
sides are quotients of `fixedPairPreimage` by its literal intersection with
`N`, so the first-isomorphism equivalence has no noncanonical choices. -/
theorem retainedFixedSoclePart_inf_pairKernel_card_eq_fixedPairSpace
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p)
    (N : LiteralNormalAxis (p := p)) :
    Nat.card
        ((S.retainedFixedSoclePart R N ⊓ S.retainedPairKernel R N) :
          Subgroup (preE7PairAction 12 p ⧸ N.1)) =
      Nat.card (S.fixedPairSpace R N) := by
  let e := surjectiveTargetEquivOfKernelEq
    (S.fixedPairIntersectionMap R N) (S.fixedPairSpaceMap R N)
    (S.fixedPairIntersectionMap_surjective R N)
    (S.fixedPairSpaceMap_surjective R N)
    (S.fixedPairIntersectionMap_ker_eq_fixedPairSpaceMap_ker R N)
  exact (Nat.card_congr e.toEquiv).trans
    (Nat.card_congr Multiplicative.toAdd)

/-! ## The fixed top image -/

theorem realizedTop_surjective
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p) :
    Function.Surjective (S.realizedTop R) :=
  R.topEquiv.symm.surjective.comp R.frame.top.rangeRestrict_surjective

/-- Pullback of the fixed socle to the original pair group. -/
def fixedTopPreimage
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p)
    (N : LiteralNormalAxis (p := p)) :
    Subgroup (preE7PairAction 12 p) :=
  (S.retainedFixedSoclePart R N).comap (QuotientGroup.mk' N.1)

noncomputable instance fixedTopPreimage_normal
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p)
    (N : LiteralNormalAxis (p := p)) :
    (S.fixedTopPreimage R N).Normal :=
  Subgroup.Normal.comap inferInstance (QuotientGroup.mk' N.1)

/-- Literal degree-twelve top image of the pulled-back fixed socle. -/
def fixedTopImage
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p)
    (N : LiteralNormalAxis (p := p)) : Subgroup D.top :=
  (S.fixedTopPreimage R N).map (S.realizedTop R)

noncomputable instance fixedTopImage_normal
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p)
    (N : LiteralNormalAxis (p := p)) :
    (S.fixedTopImage R N).Normal :=
  Subgroup.Normal.map inferInstance (S.realizedTop R)
    (S.realizedTop_surjective R)

/-- Faithful-core leaf for the top half.  A nontrivial intersection with
`S.core` would give a ternary constituent of the fixed ambient socle.  Its
commutation with the retained ternary preimage forces that constituent to
act trivially on the surviving four-plane section, contradicting `hN`.

This is the sole unfinished faithful-constituent leaf in this source-only
lane. -/
theorem fixedTopImage_inf_core_eq_bot
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p)
    (N : LiteralNormalAxis (p := p))
    (hN : ¬ S.averagingSubgroup R ≤ N.1) :
    S.fixedTopImage R N ⊓ S.core = ⊥ := by
  by_contra hK
  let K : Subgroup D.top := S.fixedTopImage R N ⊓ S.core
  letI : K.Normal := inferInstance
  have hKC : K ≤ S.core := inf_le_right
  have hKne : K ≠ ⊥ := by
    simpa only [K] using hK
  obtain ⟨u, huA, huN⟩ := SetLike.not_le_iff_exists.mp hN
  have hutop : R.frame.top u = 1 :=
    R.frame.coordinateSubgroup_le_kernel
      (S.averagingCoordinateRepresentation R).toSubmodule huA
  let ku : R.frame.top.ker := ⟨u, hutop⟩
  have hvA : R.frame.bits ku ∈ S.augmentationPlanes := by
    exact ((R.frame.kernel_mem_coordinateSubgroup
      (S.averagingCoordinateRepresentation R).toSubmodule ku).1 huA).1
  let v : S.augmentationPlanes := ⟨R.frame.bits ku, hvA⟩
  let I : Subrepresentation (S.augmentationNormalCoreRepresentation K) :=
    { toSubmodule := (R.frame.ambientAxis N.1).comap
        (S.augmentationRepresentation).toSubmodule.subtype
      apply_mem_toSubmodule := by
        intro k w hw
        change permutationFunctionRepresentation (ZMod 2) D.top (Fin 12)
            k.1 w.1 ∈ R.frame.ambientAxis N.1
        rw [R.module_action_eq]
        exact (R.frame.axisSubrepresentation N.1).apply_mem_toSubmodule
          (R.topEquiv k.1) hw }
  have hvI : v ∉ I.toSubmodule := by
    intro hv
    apply huN
    exact (R.frame.bits_mem_ambientAxis N.1 ku).mp hv
  apply S.augmentationPlanes_no_fixed_vector_mod_normalCoreSubgroup
    K hKC hKne I v hvI
  intro k
  obtain ⟨g, hgFixed, hgTop⟩ := k.2.1
  have hquA : QuotientGroup.mk' N.1 u ∈ S.retainedAveragingImage R N :=
    ⟨u, huA, rfl⟩
  have hquK : QuotientGroup.mk' N.1 u ∈ S.retainedPairKernel R N :=
    S.retainedAveragingImage_le_retainedPairKernel R N hquA
  have hquT : QuotientGroup.mk' N.1 u ∈ S.retainedTernaryImage R N :=
    S.retainedPairKernel_le_retainedTernaryImage R N hquK
  have hqgCentral : QuotientGroup.mk' N.1 g ∈
      Subgroup.centralizer
        (S.retainedTernaryImage R N : Set (preE7PairAction 12 p ⧸ N.1)) :=
    trivialActionSoclePart_le_centralizer
      (preE7PairAction 12 p ⧸ N.1) (S.retainedTernaryImage R N) hgFixed
  have hcomm : Commute (QuotientGroup.mk' N.1 g)
      (QuotientGroup.mk' N.1 u) :=
    (Subgroup.mem_centralizer_iff.mp hqgCentral _ hquT).symm
  let d : R.frame.top.ker := ku⁻¹ * MulAut.conjNormal g ku
  have hdN : (d : preE7PairAction 12 p) ∈ N.1 := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' N.1
      ((ku⁻¹ * MulAut.conjNormal g ku : R.frame.top.ker) :
        preE7PairAction 12 p) = 1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv,
      MulAut.conjNormal_apply]
    change (QuotientGroup.mk' N.1 u)⁻¹ *
      (QuotientGroup.mk' N.1 g * QuotientGroup.mk' N.1 u *
        (QuotientGroup.mk' N.1 g)⁻¹) = 1
    rw [hcomm.eq]
    group
  have hdBits : R.frame.bits d =
      R.frame.coordinateTopAction (R.frame.top.rangeRestrict g)
          (R.frame.bits ku) - R.frame.bits ku := by
    rw [R.frame.coordinateTopAction_bits]
    have hmul := congrArg Multiplicative.toAdd
      (R.frame.bitsHom.map_mul ku⁻¹ (MulAut.conjNormal g ku))
    have hinv := congrArg Multiplicative.toAdd
      (R.frame.bitsHom.map_inv ku)
    change R.frame.bits d = R.frame.bits ku⁻¹ +
      R.frame.bits (MulAut.conjNormal g ku) at hmul
    change R.frame.bits ku⁻¹ = -R.frame.bits ku at hinv
    rw [hmul, hinv, sub_eq_add_neg, add_comm]
  have htop : R.frame.top.rangeRestrict g = R.topEquiv k.1 := by
    apply R.topEquiv.symm.injective
    calc
      R.topEquiv.symm (R.frame.top.rangeRestrict g) = k.1 := hgTop
      _ = R.topEquiv.symm (R.topEquiv k.1) :=
        (R.topEquiv.symm_apply_apply k.1).symm
  change permutationFunctionRepresentation (ZMod 2) D.top (Fin 12)
      k.1 v.1 - v.1 ∈ R.frame.ambientAxis N.1
  rw [R.module_action_eq, ← htop, ← hdBits]
  exact (R.frame.bits_mem_ambientAxis N.1 d).2 hdN

/-- Once core-disjointness is established, the checked common top fact
gives the sharp order-two bound without a row-wise subgroup census. -/
theorem fixedTopImage_card_le_two
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p)
    (N : LiteralNormalAxis (p := p))
    (hN : ¬ S.averagingSubgroup R ≤ N.1) :
    Nat.card (S.fixedTopImage R N) ≤ 2 :=
  S.normal_disjoint_core_card_le_two (S.fixedTopImage R N)
    (S.fixedTopImage_inf_core_eq_bot R N hN)

/-- The image after quotienting by the retained pair kernel is a quotient
of `fixedTopImage`.  Its cardinality is therefore at most two, and one
element normally generates it. -/
theorem retainedFixedSoclePart_pairTopImage_card_le_fixedTopImage
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p)
    (N : LiteralNormalAxis (p := p)) :
    Nat.card
        ((S.retainedFixedSoclePart R N).map
          (QuotientGroup.mk' (S.retainedPairKernel R N))) ≤
      Nat.card (S.fixedTopImage R N) := by
  let P := S.fixedTopPreimage R N
  let T := (S.retainedFixedSoclePart R N).map
    (QuotientGroup.mk' (S.retainedPairKernel R N))
  let f : P →* T := {
    toFun := fun g => ⟨QuotientGroup.mk' (S.retainedPairKernel R N)
      (QuotientGroup.mk' N.1 g.1), ⟨QuotientGroup.mk' N.1 g.1, g.2, rfl⟩⟩
    map_one' := by
      apply Subtype.ext
      change QuotientGroup.mk' (S.retainedPairKernel R N)
        (QuotientGroup.mk' N.1 (1 : preE7PairAction 12 p)) = 1
      simp
    map_mul' := by
      intro g h
      apply Subtype.ext
      exact map_mul
        ((QuotientGroup.mk' (S.retainedPairKernel R N)).comp
          (QuotientGroup.mk' N.1)) g.1 h.1 }
  have hf : Function.Surjective f := by
    rintro ⟨y, ⟨x, hxH, rfl⟩⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N.1 x
    exact ⟨⟨g, hxH⟩, rfl⟩
  let g : P →* S.fixedTopImage R N :=
    (S.realizedTop R).subgroupMap P
  have hg : Function.Surjective g :=
    MonoidHom.subgroupMap_surjective (S.realizedTop R) P
  have hker : g.ker ≤ f.ker := by
    intro x hx
    apply MonoidHom.mem_ker.mpr
    apply Subtype.ext
    apply (QuotientGroup.eq_one_iff _).mpr
    change QuotientGroup.mk' N.1 (x.1 : preE7PairAction 12 p) ∈
      S.retainedPairKernel R N
    refine ⟨x.1, ?_, rfl⟩
    have htop : S.realizedTop R x.1 = 1 := by
      exact congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    have hrange : R.frame.top.rangeRestrict x.1 = 1 := by
      apply R.topEquiv.symm.injective
      simpa only [realizedTop, map_one] using htop
    exact congrArg Subtype.val hrange
  let q : P ⧸ g.ker →* T :=
    QuotientGroup.lift g.ker f (fun _ hx => MonoidHom.mem_ker.mp (hker hx))
  let e : (P ⧸ g.ker) ≃* S.fixedTopImage R N :=
    QuotientGroup.quotientKerEquivOfSurjective g hg
  let onto : S.fixedTopImage R N →* T := q.comp e.symm.toMonoidHom
  have honto : Function.Surjective onto := by
    intro y
    obtain ⟨x, rfl⟩ := hf y
    refine ⟨g x, ?_⟩
    change q (e.symm (g x)) = f x
    have he : e.symm (g x) = QuotientGroup.mk x := by
      apply e.injective
      rw [e.apply_symm_apply]
      rfl
    rw [he]
    rfl
  exact Nat.card_le_card_of_surjective onto honto

theorem retainedFixedSoclePart_pairTopImage_normalGen_le_one
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p)
    (N : LiteralNormalAxis (p := p))
    (hN : ¬ S.averagingSubgroup R ≤ N.1) :
    MarkedC4.normalGen
      ((S.retainedFixedSoclePart R N).map
        (QuotientGroup.mk' (S.retainedPairKernel R N))) ≤ 1 := by
  let T := (S.retainedFixedSoclePart R N).map
    (QuotientGroup.mk' (S.retainedPairKernel R N))
  letI : T.Normal :=
    Subgroup.Normal.map inferInstance
      (QuotientGroup.mk' (S.retainedPairKernel R N))
      (QuotientGroup.mk'_surjective (S.retainedPairKernel R N))
  have hcard : Nat.card T ≤ 2 :=
    (S.retainedFixedSoclePart_pairTopImage_card_le_fixedTopImage R N).trans
      (S.fixedTopImage_card_le_two R N hN)
  have hcases : Nat.card T = 1 ∨ Nat.card T = 2 := by
    have hpos : 0 < Nat.card T := Nat.card_pos
    omega
  have hTtwo : IsPGroup 2 T := by
    rcases hcases with hone | htwo
    · apply IsPGroup.of_card (n := 0)
      simpa only [pow_zero] using hone
    · apply IsPGroup.of_card (n := 1)
      simpa only [pow_one] using htwo
  refine (MarkedC4.normalGen_normalSubgroup_le_primeCharacterRank
    2 T hTtwo).trans ?_
  have hcharacters := primeCharacters_pow_finrank_le_card 2 T
  have hpow :
      2 ^ Module.finrank (ZMod 2) (PrimeCharacters 2 T) ≤ 2 ^ 1 := by
    simpa only [pow_one] using hcharacters.trans hcard
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < (2 : ℕ))).mp hpow

/-- The literal retained pair kernel is binary: it is an image of the
correlated flip kernel, rather than of the ambient full coordinate cube. -/
theorem retainedPairKernel_isPGroup_two
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p)
    (N : LiteralNormalAxis (p := p)) :
    IsPGroup 2 (S.retainedPairKernel R N) := by
  exact R.frame.kernel_isPGroup.map (QuotientGroup.mk' N.1)

/-- The entire fixed socle part is binary.  Its intersection with the pair
kernel is a subgroup of the binary correlated kernel, and its image above
that kernel has order at most two. -/
theorem retainedFixedSoclePart_isPGroup_two
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p)
    (N : LiteralNormalAxis (p := p))
    (hN : ¬ S.averagingSubgroup R ≤ N.1) :
    IsPGroup 2 (S.retainedFixedSoclePart R N) := by
  let H := S.retainedFixedSoclePart R N
  let E := S.retainedPairKernel R N
  let q := QuotientGroup.mk' E
  let T := H.map q
  have hTcard : Nat.card T ≤ 2 :=
    (S.retainedFixedSoclePart_pairTopImage_card_le_fixedTopImage R N).trans
      (S.fixedTopImage_card_le_two R N hN)
  have hTcases : Nat.card T = 1 ∨ Nat.card T = 2 := by
    have hpos : 0 < Nat.card T := Nat.card_pos
    omega
  have hTtwo : IsPGroup 2 T := by
    rcases hTcases with hone | htwo
    · apply IsPGroup.of_card (n := 0)
      simpa only [pow_zero] using hone
    · apply IsPGroup.of_card (n := 1)
      simpa only [pow_one] using htwo
  let f : H →* (preE7PairAction 12 p ⧸ N.1) ⧸ E := q.comp H.subtype
  have hfker : IsPGroup 2 f.ker := by
    let j : f.ker →* E :=
      { toFun := fun x ↦ ⟨x.1.1, by
          apply (QuotientGroup.eq_one_iff _).mp
          exact MonoidHom.mem_ker.mp x.2⟩
        map_one' := by rfl
        map_mul' := by intro x y; rfl }
    exact (S.retainedPairKernel_isPGroup_two R N).of_injective j (by
      intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : E ↦ z.1) hxy)
  have hpre : IsPGroup 2 (T.comap f) :=
    hTtwo.comap_of_ker_isPGroup f hfker
  have htop : T.comap f = (⊤ : Subgroup H) := by
    apply top_unique
    intro x _
    exact ⟨x.1, x.2, rfl⟩
  have htopTwo : IsPGroup 2 (⊤ : Subgroup H) := htop ▸ hpre
  exact htopTwo.of_equiv Subgroup.topEquiv

/-- The retained quotient modulo the full ternary preimage is a quotient
of the checked binary top quotient `D.top / S.core`. -/
theorem retainedTernaryQuotient_isPGroup_two
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p)
    (N : LiteralNormalAxis (p := p)) :
    IsPGroup 2
      ((preE7PairAction 12 p ⧸ N.1) ⧸ S.retainedTernaryImage R N) := by
  let U := preE7PairAction 12 p
  let Q := U ⧸ N.1
  let C := S.retainedTernaryImage R N
  let φ : U →* Q ⧸ C :=
    (QuotientGroup.mk' C).comp (QuotientGroup.mk' N.1)
  have hφ : Function.Surjective φ :=
    (QuotientGroup.mk'_surjective C).comp
      (QuotientGroup.mk'_surjective N.1)
  have hker : (S.realizedTop R).ker ≤ φ.ker := by
    intro u hu
    apply MonoidHom.mem_ker.mpr
    apply (QuotientGroup.eq_one_iff _).mpr
    change QuotientGroup.mk' N.1 u ∈ S.retainedTernaryImage R N
    refine ⟨u, ?_, rfl⟩
    change S.realizedTop R u ∈ S.core
    rw [MonoidHom.mem_ker.mp hu]
    exact Subgroup.one_mem S.core
  let ψ : D.top →* Q ⧸ C :=
    (S.realizedTop R).liftOfSurjective (S.realizedTop_surjective R) ⟨φ, hker⟩
  have hψ_apply (u : U) : ψ (S.realizedTop R u) = φ u := by
    exact MonoidHom.liftOfRightInverse_comp_apply
      (S.realizedTop R) (Function.surjInv (S.realizedTop_surjective R))
        (Function.rightInverse_surjInv (S.realizedTop_surjective R)) ⟨φ, hker⟩ u
  have hψ : Function.Surjective ψ := by
    intro y
    obtain ⟨u, rfl⟩ := hφ y
    exact ⟨S.realizedTop R u, hψ_apply u⟩
  have hcore : S.core ≤ ψ.ker := by
    intro c hc
    obtain ⟨u, hu⟩ := S.realizedTop_surjective R c
    apply MonoidHom.mem_ker.mpr
    rw [← hu]
    rw [hψ_apply]
    apply (QuotientGroup.eq_one_iff _).mpr
    change QuotientGroup.mk' N.1 u ∈ S.retainedTernaryImage R N
    refine ⟨u, ?_, rfl⟩
    change S.realizedTop R u ∈ S.core
    rw [hu]
    exact hc
  let psiBar : D.top ⧸ S.core →* Q ⧸ C :=
    QuotientGroup.lift S.core ψ (fun _ hc ↦ MonoidHom.mem_ker.mp (hcore hc))
  have hpsiBar : Function.Surjective psiBar := by
    intro y
    obtain ⟨g, rfl⟩ := hψ y
    exact ⟨QuotientGroup.mk' S.core g, rfl⟩
  exact S.quotient_binary.of_surjective psiBar hpsiBar

/-- A binary ambient minimal normal subgroup centralized by `C` is central
as soon as the remaining ambient quotient is binary.  The proof is the
fixed-point theorem for a finite two-group acting on the nonidentity
elements of the minimal normal subgroup. -/
private theorem minimalNormal_le_center_of_binary_quotient
    {Q : Type} [Group Q] [Finite Q]
    (C M : Subgroup Q) [C.Normal]
    (hquot : IsPGroup 2 (Q ⧸ C))
    (hM : IsMinimalNormalSubgroup M)
    (hMtwo : IsPGroup 2 M)
    (hMC : M ≤ Subgroup.centralizer (C : Set Q)) :
    M ≤ Subgroup.center Q := by
  letI : M.Normal := hM.1
  let α0 : Q →* MulAut M := MulAut.conjNormal
  have hCker : C ≤ α0.ker := by
    intro c hc
    apply MonoidHom.mem_ker.mpr
    apply MulEquiv.ext
    intro m
    apply Subtype.ext
    simp only [α0, MulAut.conjNormal_apply, MulAut.one_apply]
    have hcomm : Commute (m.1 : Q) c :=
      (Subgroup.mem_centralizer_iff.mp (hMC m.2) c hc).symm
    rw [← hcomm.eq]
    group
  let α : Q ⧸ C →* MulAut M :=
    QuotientGroup.lift C α0 (fun _ hc ↦ MonoidHom.mem_ker.mp (hCker hc))
  letI : MulAction (Q ⧸ C) M :=
    { smul := fun g m ↦ α g m
      one_smul := by intro m; change α 1 m = m; simp
      mul_smul := by
        intro g h m
        change α (g * h) m = α g (α h m)
        rw [map_mul]
        rfl }
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hMtwo
  have haPos : 0 < a := by
    by_contra ha0
    have : Nat.card M = 1 := by
      rw [ha, Nat.eq_zero_of_not_pos ha0, pow_zero]
    exact hM.2.1 (Subgroup.card_eq_one.mp this)
  have hdiv : 2 ∣ Nat.card M := by
    rw [ha]
    exact dvd_pow_self 2 haPos.ne'
  have hone : (1 : M) ∈ MulAction.fixedPoints (Q ⧸ C) M := by
    intro g
    exact map_one (α g)
  obtain ⟨m, hmFixed, hOneNe⟩ :=
    hquot.exists_fixed_point_of_prime_dvd_card_of_fixed_point M hdiv hone
  have hmNe : m ≠ 1 := Ne.symm hOneNe
  have hmCenter : (m.1 : Q) ∈ Subgroup.center Q := by
    apply Subgroup.mem_center_iff.mpr
    intro g
    have hfix := hmFixed (QuotientGroup.mk' C g)
    change α (QuotientGroup.mk' C g) m = m at hfix
    have hconj : MulAut.conjNormal g m = m := by
      simpa only [α, QuotientGroup.lift_mk] using hfix
    exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val hconj)
  have hInfNe : M ⊓ Subgroup.center Q ≠ ⊥ := by
    intro hbot
    have hmBot : (m.1 : Q) ∈ (⊥ : Subgroup Q) := by
      rw [← hbot]
      exact ⟨m.2, hmCenter⟩
    exact hmNe (Subtype.ext (Subgroup.mem_bot.mp hmBot))
  have hInfEq : M ⊓ Subgroup.center Q = M :=
    hM.2.2 (M ⊓ Subgroup.center Q) inferInstance hInfNe inf_le_left
  intro m hm
  have : m ∈ M ⊓ Subgroup.center Q := by
    rw [hInfEq]
    exact hm
  exact this.2

/-- The fixed socle is actually central in the retained quotient.  Every
selected minimal factor is binary by the preceding extension argument;
the ternary image centralizes it by definition, and the remaining quotient
is the checked binary top quotient. -/
theorem retainedFixedSoclePart_le_center
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p)
    (N : LiteralNormalAxis (p := p))
    (hN : ¬ S.averagingSubgroup R ≤ N.1) :
    S.retainedFixedSoclePart R N ≤
      Subgroup.center (preE7PairAction 12 p ⧸ N.1) := by
  let Q := preE7PairAction 12 p ⧸ N.1
  let C := S.retainedTernaryImage R N
  have hfixedTwo := S.retainedFixedSoclePart_isPGroup_two R N hN
  have hquot := S.retainedTernaryQuotient_isPGroup_two R N
  unfold retainedFixedSoclePart trivialActionSoclePart
  apply minimalNormalSoclePart_le_of
  intro M hM hMfixed
  have hMle : M ≤ S.retainedFixedSoclePart R N :=
    minimalNormal_le_minimalNormalSoclePart
      (fun L : Subgroup Q ↦ ¬ ⁅C, L⁆ = L) M hM hMfixed
  have hMtwo : IsPGroup 2 M := hfixedTwo.to_le hMle
  have hcommBot : ⁅C, M⁆ = ⊥ :=
    (minimalNormal_commutator_full_or_trivial C M hM).resolve_left hMfixed
  have hMC : M ≤ Subgroup.centralizer (C : Set Q) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
    simpa only [Subgroup.commutator_comm] using hcommBot
  exact minimalNormal_le_center_of_binary_quotient C M hquot hM hMtwo hMC

/-! ## The four-block Reynolds quotient -/

/-- The actual core orbit containing a point, expressed in the acted-on
four-block model. -/
def pointBlock (x : Fin 12) : S.Blocks := by
  letI : MulAction.IsPretransitive D.top (Fin 12) := S.top_transitive
  refine ⟨MulAction.orbit S.core x, ?_⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq D.top (0 : Fin 12) x
  refine ⟨g, ?_⟩
  change g • (MulAction.orbit S.core (0 : Fin 12) : Set (Fin 12)) =
    MulAction.orbit S.core x
  rw [MulAction.smul_orbit_eq_orbit_smul, hg]

theorem coe_pointBlock (x : Fin 12) :
    (S.pointBlock x : Set (Fin 12)) = MulAction.orbit S.core x :=
  by simp only [pointBlock]

theorem pointBlock_smul (g : D.top) (x : Fin 12) :
    S.pointBlock (g • x) = g • S.pointBlock x := by
  apply Subtype.ext
  change MulAction.orbit S.core (g • x) =
    g • (S.pointBlock x : Set (Fin 12))
  rw [S.coe_pointBlock]
  exact (MulAction.smul_orbit_eq_orbit_smul S.core x g).symm

theorem pointBlock_eq_of_mem (B : S.Blocks) (x : Fin 12)
    (hx : x ∈ (B : Set (Fin 12))) : S.pointBlock x = B := by
  letI : MulAction.IsPretransitive D.top (Fin 12) := S.top_transitive
  apply Subtype.ext
  rw [S.coe_pointBlock]
  obtain ⟨g, hg⟩ := B.property
  have hx' : x ∈ MulAction.orbit S.core (g • (0 : Fin 12)) := by
    have hxg : x ∈ g • MulAction.orbit S.core (0 : Fin 12) := by
      change x ∈
        (fun m : D.top ↦ m • MulAction.orbit S.core (0 : Fin 12)) g
      rw [hg]
      exact hx
    rw [MulAction.smul_orbit_eq_orbit_smul] at hxg
    exact hxg
  calc
    MulAction.orbit S.core x = MulAction.orbit S.core (g • (0 : Fin 12)) :=
      MulAction.orbit_eq_iff.mpr hx'
    _ = g • (MulAction.orbit S.core (0 : Fin 12) : Set (Fin 12)) :=
      (MulAction.smul_orbit_eq_orbit_smul S.core (0 : Fin 12) g).symm
    _ = (B : Set (Fin 12)) := hg

/-- Inflate a function on the four core orbits to the corresponding
core-constant function on the twelve literal points. -/
def blockConstant :
    (S.Blocks → ZMod 2) →ₗ[ZMod 2] (Fin 12 → ZMod 2) where
  toFun f x := f (S.pointBlock x)
  map_add' f g := by
    funext x
    rfl
  map_smul' a f := by
    funext x
    rfl

theorem blockOrbitParity_blockConstant (f : S.Blocks → ZMod 2) :
    S.blockOrbitParity (S.blockConstant f) = f := by
  funext B
  change (∑ x : B.1, f (S.pointBlock x.1)) = f B
  have hconst : ∀ x : B.1, f (S.pointBlock x.1) = f B := by
    intro x
    rw [S.pointBlock_eq_of_mem B x.1 x.2]
  simp_rw [hconst]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_eq_nat_card]
  have hcard : Nat.card B.1 = 3 := by
    obtain ⟨g, hg⟩ := B.property
    have hset : (B.1 : Set (Fin 12)) =
        MulAction.orbit S.core (g • (0 : Fin 12)) := by
      calc
        (B.1 : Set (Fin 12)) =
            g • (MulAction.orbit S.core (0 : Fin 12) : Set (Fin 12)) := hg.symm
        _ = MulAction.orbit S.core (g • (0 : Fin 12)) :=
          MulAction.smul_orbit_eq_orbit_smul S.core (0 : Fin 12) g
    rw [hset]
    let o : S.OrbitBlocks := Quotient.mk'' (g • (0 : Fin 12))
    simpa only [o, MulAction.orbitRel.Quotient.orbit_mk] using
      S.orbit_card_eq_three o
  rw [hcard]
  have htwo : ∀ z : ZMod 2, 2 • z = 0 := by decide
  rw [show (3 : ℕ) = 2 + 1 by norm_num, add_nsmul, htwo,
    zero_add, one_nsmul]

theorem blockConstant_core_fixed (c : S.core) (f : S.Blocks → ZMod 2) :
    permutationFunctionRepresentation (ZMod 2) D.top (Fin 12) c.1
        (S.blockConstant f) = S.blockConstant f := by
  funext x
  change f (S.pointBlock ((c.1)⁻¹ • x)) = f (S.pointBlock x)
  rw [S.pointBlock_smul]
  have hc : ((c.1)⁻¹ : D.top) • S.pointBlock x = S.pointBlock x := by
    simpa only [Subgroup.coe_inv] using S.core_smul_block c⁻¹ (S.pointBlock x)
  rw [hc]

theorem blockConstant_blockOrbitParity_of_core_fixed
    (v : Fin 12 → ZMod 2)
    (hv : ∀ c : S.core,
      permutationFunctionRepresentation (ZMod 2) D.top (Fin 12) c.1 v = v) :
    S.blockConstant (S.blockOrbitParity v) = v := by
  funext x
  change (∑ y : (S.pointBlock x).1, v y.1) = v x
  have hconst : ∀ y : (S.pointBlock x).1, v y.1 = v x := by
    intro y
    have hy : y.1 ∈ MulAction.orbit S.core x := by
      rw [← S.coe_pointBlock]
      exact y.2
    obtain ⟨c, hc⟩ := hy
    have hfix := congrFun (hv c⁻¹) x
    simp only [permutationFunctionRepresentation_apply, Subgroup.coe_inv,
      inv_inv] at hfix
    rw [← hc]
    exact hfix
  simp_rw [hconst]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_eq_nat_card]
  have hcard : Nat.card (S.pointBlock x).1 = 3 := by
    let o : S.OrbitBlocks := Quotient.mk'' x
    rw [S.coe_pointBlock]
    simpa only [o, MulAction.orbitRel.Quotient.orbit_mk] using
      S.orbit_card_eq_three o
  rw [hcard]
  have htwo : ∀ z : ZMod 2, 2 • z = 0 := by decide
  rw [show (3 : ℕ) = 2 + 1 by norm_num, add_nsmul, htwo,
    zero_add, one_nsmul]

/-- The natural action on the four core orbits factors through the binary
quotient `D.top / S.core`. -/
def blockQuotientAction : D.top ⧸ S.core →* Equiv.Perm S.Blocks :=
  QuotientGroup.lift S.core (MulAction.toPermHom D.top S.Blocks) (by
    intro c hc
    apply Equiv.ext
    intro B
    exact S.core_smul_block ⟨c, hc⟩ B)

noncomputable instance blockQuotientMulAction :
    MulAction (D.top ⧸ S.core) S.Blocks where
  smul q B := S.blockQuotientAction q B
  one_smul B := by
    change S.blockQuotientAction 1 B = B
    rw [map_one]
    rfl
  mul_smul q r B := by
    change S.blockQuotientAction (q * r) B =
      S.blockQuotientAction q (S.blockQuotientAction r B)
    rw [map_mul]
    rfl

theorem blockQuotientAction_mk (g : D.top) (B : S.Blocks) :
    (QuotientGroup.mk' S.core g) • B = g • B := by
  rfl

noncomputable instance blockQuotientPretransitive :
    MulAction.IsPretransitive (D.top ⧸ S.core) S.Blocks := by
  letI : MulAction.IsPretransitive D.top (Fin 12) := S.top_transitive
  constructor
  intro B C
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq D.top B C
  exact ⟨QuotientGroup.mk' S.core g, by
    simpa only [S.blockQuotientAction_mk] using hg⟩

theorem blockConstant_action (g : D.top) (f : S.Blocks → ZMod 2) :
    permutationFunctionRepresentation (ZMod 2) D.top (Fin 12) g
        (S.blockConstant f) =
      S.blockConstant
        (permutationFunctionRepresentation (ZMod 2)
          (D.top ⧸ S.core) S.Blocks (QuotientGroup.mk' S.core g) f) := by
  funext x
  change f (S.pointBlock (g⁻¹ • x)) =
    f ((QuotientGroup.mk' S.core g)⁻¹ • S.pointBlock x)
  rw [S.pointBlock_smul]
  rfl

/-- Centrality of the retained fixed socle says exactly that every lift of
one of its pair-kernel vectors has displacement in the original normal
axis.  This is the bridge from the group-theoretic fixed part to the
literal natural permutation module. -/
theorem fixedPairSpace_displacement
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p)
    (N : LiteralNormalAxis (p := p))
    (hN : ¬ S.averagingSubgroup R ≤ N.1)
    (g : D.top) (v : R.frame.kernelSpace)
    (hv : (R.frame.normalSpace N.1).mkQ v ∈ S.fixedPairSpace R N) :
    permutationFunctionRepresentation (ZMod 2) D.top (Fin 12) g v.1 - v.1 ∈
      R.frame.ambientAxis N.1 := by
  obtain ⟨u, hu⟩ := S.realizedTop_surjective R g
  obtain ⟨k, hk⟩ := R.frame.kernelSpaceHom_bijective.2
    (Multiplicative.ofAdd v)
  have hkAdd : (R.frame.kernelSpaceHom k).toAdd = v :=
    congrArg Multiplicative.toAdd hk
  have hkFixed : k ∈ S.fixedPairPreimage R N := by
    apply (sectionSubgroupImage_mem_iff (p := 2)
      (R.frame.sectionMap N.1) (S.fixedPairPreimage R N)
      (by
        rw [R.frame.sectionMap_ker]
        exact S.normalSubgroupOfPairKernel_le_fixedPairPreimage R N) k).mp
    change (R.frame.normalSpace N.1).mkQ
      (R.frame.kernelSpaceHom k).toAdd ∈ S.fixedPairSpace R N
    rw [hkAdd]
    exact hv
  have hkCenter : QuotientGroup.mk' N.1 (k.1 : preE7PairAction 12 p) ∈
      Subgroup.center (preE7PairAction 12 p ⧸ N.1) :=
    S.retainedFixedSoclePart_le_center R N hN hkFixed
  let d : R.frame.top.ker := k⁻¹ * MulAut.conjNormal u k
  have hdN : (d : preE7PairAction 12 p) ∈ N.1 := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' N.1
      ((k⁻¹ * MulAut.conjNormal u k : R.frame.top.ker) :
        preE7PairAction 12 p) = 1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv,
      MulAut.conjNormal_apply]
    rw [Subgroup.mem_center_iff.mp hkCenter (QuotientGroup.mk' N.1 u)]
    group
  have htop : R.frame.top.rangeRestrict u = R.topEquiv g := by
    apply R.topEquiv.symm.injective
    simpa only [realizedTop, R.topEquiv.symm_apply_apply] using hu
  rw [R.module_action_eq, ← htop, ← hkAdd]
  change R.frame.coordinateTopAction (R.frame.top.rangeRestrict u)
      (R.frame.bits k) - R.frame.bits k ∈ R.frame.ambientAxis N.1
  rw [← R.frame.bits_commutator]
  exact (R.frame.bits_mem_ambientAxis N.1 d).2 hdN

/-- Every vector of the fixed pair section has a representative in the
correlated kernel which is fixed by the ternary core.  Maschke supplies a
core-stable complement to the original normal axis; centrality makes the
complement component fixed, and the odd-core hypothesis makes the splitting
available in characteristic two. -/
theorem fixedPairSpace_exists_coreFixed_rep
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p)
    (N : LiteralNormalAxis (p := p))
    (hN : ¬ S.averagingSubgroup R ≤ N.1)
    (s : S.fixedPairSpace R N) :
    ∃ v : R.frame.kernelSpace,
      (R.frame.normalSpace N.1).mkQ v = s.1 ∧
      ∀ c : S.core,
        permutationFunctionRepresentation (ZMod 2) D.top (Fin 12) c.1 v.1 =
          v.1 := by
  obtain ⟨v, hv⟩ := (R.frame.normalSpace N.1).mkQ_surjective s.1
  let ρ := (permutationFunctionRepresentation
    (ZMod 2) D.top (Fin 12)).comp S.core.subtype
  let I : Subrepresentation ρ := {
    toSubmodule := R.frame.ambientAxis N.1
    apply_mem_toSubmodule := by
      intro c x hx
      change permutationFunctionRepresentation (ZMod 2) D.top (Fin 12)
          c.1 x ∈ R.frame.ambientAxis N.1
      rw [R.module_action_eq]
      exact (R.frame.axisSubrepresentation N.1).apply_mem_toSubmodule
        (R.topEquiv c.1) hx }
  have hcoreThree : IsPGroup 3 S.core :=
    S.coreSubgroup_isPGroup_three S.core le_rfl
  obtain ⟨a, hcard⟩ := IsPGroup.iff_card.mp hcoreThree
  letI : NeZero (Nat.card S.core : ZMod 2) := by
    constructor
    intro hzero
    have hdiv : 2 ∣ Nat.card S.core := (ZMod.natCast_eq_zero_iff _ _).mp hzero
    rw [hcard] at hdiv
    have : 2 ∣ 3 := Nat.prime_two.dvd_of_dvd_pow hdiv
    norm_num at this
  obtain ⟨J, hIJ⟩ := exists_isCompl I
  have hvSup : v.1 ∈ I.toSubmodule ⊔ J.toSubmodule := by
    have hvTop : v.1 ∈ (⊤ : Subrepresentation ρ) := Submodule.mem_top
    rw [← hIJ.codisjoint.eq_top] at hvTop
    exact hvTop
  obtain ⟨i, hi, j, hj, hij⟩ := Submodule.mem_sup.mp hvSup
  have hjfixed : ∀ c : S.core, ρ c j = j := by
    intro c
    have hvFixedMod : ρ c v.1 - v.1 ∈ I := by
      apply S.fixedPairSpace_displacement R N hN c.1 v
      rw [hv]
      exact s.2
    have hiDiff : ρ c i - i ∈ I :=
      I.toSubmodule.sub_mem (I.apply_mem_toSubmodule c hi) hi
    have hjDiffI : ρ c j - j ∈ I := by
      have heq : ρ c j - j = (ρ c v.1 - v.1) - (ρ c i - i) := by
        rw [← hij, map_add]
        simp only [sub_eq_add_neg, neg_smul, one_smul]
        abel
      rw [heq]
      exact I.toSubmodule.sub_mem hvFixedMod hiDiff
    have hjDiffJ : ρ c j - j ∈ J :=
      J.toSubmodule.sub_mem (J.apply_mem_toSubmodule c hj) hj
    have hzero : ρ c j - j = 0 := by
      have hInf : ρ c j - j ∈ (I ⊓ J : Subrepresentation ρ) :=
        ⟨hjDiffI, hjDiffJ⟩
      rw [hIJ.disjoint.eq_bot] at hInf
      simpa only [Submodule.mem_bot] using hInf
    exact sub_eq_zero.mp hzero
  have hiKernel : i ∈ R.frame.kernelSpace :=
    R.frame.ambientAxis_le_kernelSpace N.1 hi
  have hjKernel : j ∈ R.frame.kernelSpace := by
    have hj : j = v.1 - i := by
      rw [← hij]
      abel
    rw [hj]
    exact R.frame.kernelSpace.sub_mem v.2 hiKernel
  let jK : R.frame.kernelSpace := ⟨j, hjKernel⟩
  have hjq : (R.frame.normalSpace N.1).mkQ jK = s.1 := by
    rw [← hv]
    apply (Submodule.Quotient.eq _).mpr
    have hiMap : i ∈ (R.frame.normalSpace N.1).map
        R.frame.kernelSpace.subtype := by
      rw [normalSpace_map_subtype_eq_ambientAxis]
      exact hi
    obtain ⟨m, hm, hmi⟩ := hiMap
    have hdiff : jK - v = -m := by
      apply Subtype.ext
      change j - v.1 = -(m : R.frame.kernelSpace).1
      rw [← hij, ← hmi]
      abel
    rw [hdiff]
    exact (R.frame.normalSpace N.1).neg_mem hm
  exact ⟨jK, hjq, hjfixed⟩

/-- Four-block functions whose core-constant inflations respect the actual
correlated pair kernel. -/
def blockKernelSpace
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p) :
    Submodule (ZMod 2) (S.Blocks → ZMod 2) :=
  R.frame.kernelSpace.comap S.blockConstant

/-- Include a compatible four-block function into the actual correlated
kernel coordinates. -/
def blockKernelEmbedding
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p) :
    S.blockKernelSpace R →ₗ[ZMod 2] R.frame.kernelSpace where
  toFun w := ⟨S.blockConstant w.1, w.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Send a compatible four-block function to the original pair section. -/
def blockSectionMap
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p)
    (N : LiteralNormalAxis (p := p)) :
    S.blockKernelSpace R →ₗ[ZMod 2]
      (R.frame.kernelSpace ⧸ R.frame.normalSpace N.1) :=
  (R.frame.normalSpace N.1).mkQ.comp (S.blockKernelEmbedding R)

/-- The domain in compatible block functions which maps into the fixed pair
section. -/
def fixedBlockDomain
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p)
    (N : LiteralNormalAxis (p := p)) :
    Submodule (ZMod 2) (S.blockKernelSpace R) :=
  (S.fixedPairSpace R N).comap (S.blockSectionMap R N)

/-- The corresponding literal subspace of the four-block permutation
module. -/
def fixedBlockSpace
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p)
    (N : LiteralNormalAxis (p := p)) :
    Submodule (ZMod 2) (S.Blocks → ZMod 2) :=
  (S.fixedBlockDomain R N).map (S.blockKernelSpace R).subtype

private def fixedBlockEquiv
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p)
    (N : LiteralNormalAxis (p := p)) :
    S.fixedBlockDomain R N ≃ₗ[ZMod 2] S.fixedBlockSpace R N :=
  (S.blockKernelSpace R).equivSubtypeMap (S.fixedBlockDomain R N)

/-- The exact fixed pair-section value carried by a vector in the selected
four-block subspace. -/
def fixedBlockQuotientMap
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p)
    (N : LiteralNormalAxis (p := p)) :
    S.fixedBlockSpace R N →ₗ[ZMod 2] S.fixedPairSpace R N :=
  (((S.blockSectionMap R N).domRestrict
      (S.fixedBlockDomain R N)).codRestrict
        (S.fixedPairSpace R N) (fun w ↦ w.2)).comp
    (S.fixedBlockEquiv R N).symm.toLinearMap

theorem fixedBlockQuotientMap_surjective
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p)
    (N : LiteralNormalAxis (p := p))
    (hN : ¬ S.averagingSubgroup R ≤ N.1) :
    Function.Surjective (S.fixedBlockQuotientMap R N) := by
  intro s
  obtain ⟨v, hvq, hvFixed⟩ :=
    S.fixedPairSpace_exists_coreFixed_rep R N hN s
  let w : S.Blocks → ZMod 2 := S.blockOrbitParity v.1
  have hwConst : S.blockConstant w = v.1 :=
    S.blockConstant_blockOrbitParity_of_core_fixed v.1 hvFixed
  have hwKernel : w ∈ S.blockKernelSpace R := by
    change S.blockConstant w ∈ R.frame.kernelSpace
    rw [hwConst]
    exact v.2
  let wK : S.blockKernelSpace R := ⟨w, hwKernel⟩
  have hwSection : S.blockSectionMap R N wK = s.1 := by
    change (R.frame.normalSpace N.1).mkQ
      ⟨S.blockConstant w, hwKernel⟩ = s.1
    calc
      (R.frame.normalSpace N.1).mkQ ⟨S.blockConstant w, hwKernel⟩ =
          (R.frame.normalSpace N.1).mkQ v := by
        apply congrArg ((R.frame.normalSpace N.1).mkQ)
        exact Subtype.ext hwConst
      _ = s.1 := hvq
  let d : S.fixedBlockDomain R N := ⟨wK, by
    change S.blockSectionMap R N wK ∈ S.fixedPairSpace R N
    rw [hwSection]
    exact s.2⟩
  refine ⟨S.fixedBlockEquiv R N d, ?_⟩
  apply Subtype.ext
  change S.blockSectionMap R N d.1 = s.1
  exact hwSection

private theorem blockSectionMap_eq_of_ambientAxis_displacement
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p)
    (N : LiteralNormalAxis (p := p))
    (x y : S.blockKernelSpace R)
    (hxy : S.blockConstant x.1 - S.blockConstant y.1 ∈
      R.frame.ambientAxis N.1) :
    S.blockSectionMap R N x = S.blockSectionMap R N y := by
  apply (Submodule.Quotient.eq _).mpr
  have hmap : S.blockConstant x.1 - S.blockConstant y.1 ∈
      (R.frame.normalSpace N.1).map R.frame.kernelSpace.subtype := by
    rw [normalSpace_map_subtype_eq_ambientAxis]
    exact hxy
  obtain ⟨m, hm, hmval⟩ := hmap
  have hdiff : S.blockKernelEmbedding R x - S.blockKernelEmbedding R y = m := by
    apply Subtype.ext
    exact hmval.symm
  rw [hdiff]
  exact hm

private theorem fixedBlock_action_lift
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p)
    (N : LiteralNormalAxis (p := p))
    (hN : ¬ S.averagingSubgroup R ≤ N.1)
    (g : D.top) (w : S.fixedBlockDomain R N) :
    ∃ w' : S.fixedBlockDomain R N,
      (w'.1.1 : S.Blocks → ZMod 2) =
        permutationFunctionRepresentation (ZMod 2)
          (D.top ⧸ S.core) S.Blocks (QuotientGroup.mk' S.core g) w.1.1 ∧
      S.blockSectionMap R N w'.1 = S.blockSectionMap R N w.1 := by
  let gw : S.Blocks → ZMod 2 :=
    permutationFunctionRepresentation (ZMod 2)
      (D.top ⧸ S.core) S.Blocks (QuotientGroup.mk' S.core g) w.1.1
  have hdisp : permutationFunctionRepresentation (ZMod 2) D.top (Fin 12) g
        (S.blockConstant w.1.1) - S.blockConstant w.1.1 ∈
      R.frame.ambientAxis N.1 := by
    apply S.fixedPairSpace_displacement R N hN g
      (S.blockKernelEmbedding R w.1)
    exact w.2
  have hgwKernel : gw ∈ S.blockKernelSpace R := by
    change S.blockConstant gw ∈ R.frame.kernelSpace
    have haction := S.blockConstant_action g w.1.1
    change _ = S.blockConstant gw at haction
    rw [← haction]
    have hdelta : permutationFunctionRepresentation (ZMod 2) D.top (Fin 12) g
          (S.blockConstant w.1.1) - S.blockConstant w.1.1 ∈
        R.frame.kernelSpace :=
      R.frame.ambientAxis_le_kernelSpace N.1 hdisp
    simpa only [sub_add_cancel] using
      R.frame.kernelSpace.add_mem hdelta w.1.2
  let gwK : S.blockKernelSpace R := ⟨gw, hgwKernel⟩
  have hsection : S.blockSectionMap R N gwK =
      S.blockSectionMap R N w.1 := by
    apply S.blockSectionMap_eq_of_ambientAxis_displacement R N
    have haction := S.blockConstant_action g w.1.1
    change _ = S.blockConstant gw at haction
    rw [← haction]
    exact hdisp
  have hgwFixed : gwK ∈ S.fixedBlockDomain R N := by
    change S.blockSectionMap R N gwK ∈ S.fixedPairSpace R N
    rw [hsection]
    exact w.2
  exact ⟨⟨gwK, hgwFixed⟩, rfl, hsection⟩

/-- The fixed block preimage is a subrepresentation for the binary quotient
action on the four actual ternary blocks. -/
def fixedBlockSubrepresentation
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p)
    (N : LiteralNormalAxis (p := p))
    (hN : ¬ S.averagingSubgroup R ≤ N.1) :
    Subrepresentation
      (permutationFunctionRepresentation (ZMod 2)
        (D.top ⧸ S.core) S.Blocks) where
  toSubmodule := S.fixedBlockSpace R N
  apply_mem_toSubmodule := by
    intro q w hw
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective S.core q
    let e := S.fixedBlockEquiv R N
    let d : S.fixedBlockDomain R N := e.symm ⟨w, hw⟩
    obtain ⟨d', hd', _⟩ := S.fixedBlock_action_lift R N hN g d
    refine ⟨d', d'.2, ?_⟩
    have hdw : d.1.1 = w := by
      exact congrArg Subtype.val (e.apply_symm_apply ⟨w, hw⟩)
    change d'.1.1 =
      permutationFunctionRepresentation (ZMod 2)
        (D.top ⧸ S.core) S.Blocks (QuotientGroup.mk' S.core g) w
    rw [hd', hdw]

theorem fixedBlockQuotientMap_trivial
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p)
    (N : LiteralNormalAxis (p := p))
    (hN : ¬ S.averagingSubgroup R ≤ N.1)
    (q : D.top ⧸ S.core)
    (w : (S.fixedBlockSubrepresentation R N hN).toSubmodule) :
    S.fixedBlockQuotientMap R N
        ((S.fixedBlockSubrepresentation R N hN).toRepresentation q w) =
      S.fixedBlockQuotientMap R N w := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective S.core q
  let e := S.fixedBlockEquiv R N
  let d : S.fixedBlockDomain R N := e.symm w
  obtain ⟨d', hdAction, hdSection⟩ :=
    S.fixedBlock_action_lift R N hN g d
  have hrep :
      (S.fixedBlockSubrepresentation R N hN).toRepresentation
          (QuotientGroup.mk' S.core g) w = e d' := by
    apply Subtype.ext
    exact hdAction.symm
  rw [hrep]
  rw [show w = e d by exact (e.apply_symm_apply w).symm]
  apply Subtype.ext
  change S.blockSectionMap R N d'.1 = S.blockSectionMap R N d.1
  exact hdSection

/-- Four-block permutation-module leaf.  Block parity sends the upper and
lower preimages of `fixedPairSpace` to invariant subspaces of
`S.Blocks → ZMod 2`.  The displayed core acts trivially on the four
blocks, and the remaining action is the transitive two-group
`D.top / S.core`.  The section is trivial because it is selected from the
core-central ambient socle.  Thus
`twoGroup_permutation_trivial_section_finrank_le` with `t = 2` gives the
bound `2.choose 1 = 2`.

The preceding Reynolds construction supplies the required exact quotient
map without any auxiliary hypothesis. -/
theorem fixedPairSpace_finrank_le_two
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p)
    (N : LiteralNormalAxis (p := p))
    (hN : ¬ S.averagingSubgroup R ≤ N.1) :
    Module.finrank (ZMod 2) (S.fixedPairSpace R N) ≤ 2 := by
  have hbound := twoGroup_permutation_trivial_quotient_finrank_le
    (k := ZMod 2) S.quotient_binary 2 (by
      rw [S.blocks_card]
      norm_num) (S.pointBlock (0 : Fin 12))
    (S.fixedBlockSubrepresentation R N hN)
    (S.fixedBlockQuotientMap R N)
    (S.fixedBlockQuotientMap_surjective R N hN)
    (S.fixedBlockQuotientMap_trivial R N hN)
  norm_num at hbound ⊢
  exact hbound


/-- Transport of the preceding literal section dimension through
`BinaryPairFrame.sectionMap`.  The exact cardinal identity makes the
intersection a two-group of order `2^d`; Burnside's basis bound then costs
at most its vector-space dimension. -/
theorem retainedFixedSoclePart_inf_pairKernel_normalGen_le_two
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p)
    (N : LiteralNormalAxis (p := p))
    (hN : ¬ S.averagingSubgroup R ≤ N.1) :
    MarkedC4.normalGen
      (S.retainedFixedSoclePart R N ⊓ S.retainedPairKernel R N) ≤ 2 := by
  let H := S.retainedFixedSoclePart R N ⊓ S.retainedPairKernel R N
  let V := S.fixedPairSpace R N
  letI : H.Normal := inferInstance
  have hcardV : Nat.card V =
      2 ^ Module.finrank (ZMod 2) V := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have hcardH : Nat.card H =
      2 ^ Module.finrank (ZMod 2) V := by
    change Nat.card
        ((S.retainedFixedSoclePart R N ⊓ S.retainedPairKernel R N) :
          Subgroup (preE7PairAction 12 p ⧸ N.1)) =
      2 ^ Module.finrank (ZMod 2) (S.fixedPairSpace R N)
    rw [S.retainedFixedSoclePart_inf_pairKernel_card_eq_fixedPairSpace R N,
      hcardV]
  have hHtwo : IsPGroup 2 H :=
    IsPGroup.of_card hcardH
  refine (MarkedC4.normalGen_normalSubgroup_le_primeCharacterRank
    2 H hHtwo).trans ?_
  have hcharacters := primeCharacters_pow_finrank_le_card 2 H
  rw [hcardH] at hcharacters
  have hrank : Module.finrank (ZMod 2) (PrimeCharacters 2 H) ≤
      Module.finrank (ZMod 2) V :=
    (Nat.pow_le_pow_iff_right (by norm_num : 1 < (2 : ℕ))).mp hcharacters
  exact hrank.trans (S.fixedPairSpace_finrank_le_two R N hN)


/-! ## The `2 + 1` fixed-socle bound -/

/-- Split at the literal retained pair kernel.  The correlated fixed
section costs two positions and its core-disjoint top image costs one. -/
theorem retainedFixedSoclePart_normalGen_le_three
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p)
    (N : LiteralNormalAxis (p := p))
    (hN : ¬ S.averagingSubgroup R ≤ N.1) :
    MarkedC4.normalGen (S.retainedFixedSoclePart R N) ≤ 3 := by
  have hsplit := MarkedC4.normalGen_normal_le_inter_add_image
    (S.retainedFixedSoclePart R N) (S.retainedPairKernel R N)
  exact hsplit.trans (by
    have hpair :=
      S.retainedFixedSoclePart_inf_pairKernel_normalGen_le_two R N hN
    have htop :=
      S.retainedFixedSoclePart_pairTopImage_normalGen_le_one R N hN
    omega)

/-- Exact `fixed` field required by `RetainedSoclePartsBounds`; no
additional hypothesis is exposed at the assembly boundary. -/
theorem retainedSoclePartsBounds_fixed :
    ∀ (p : PreE7PairActionClass 12)
      (R : DegreeTwoPairTopRealization D p)
      (N : LiteralNormalAxis (p := p)),
      ¬ S.averagingSubgroup R ≤ N.1 →
        MarkedC4.normalGen
          (trivialActionSoclePart (preE7PairAction 12 p ⧸ N.1)
            (S.retainedTernaryImage R N)) ≤ 3 := by
  intro p R N hN
  exact S.retainedFixedSoclePart_normalGen_le_three R N hN

end DegreeTwoFourTernaryTopStructure
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
