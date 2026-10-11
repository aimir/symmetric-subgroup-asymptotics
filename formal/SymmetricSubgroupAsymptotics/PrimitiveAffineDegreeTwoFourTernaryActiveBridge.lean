import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoFourTernaryFixedSocle
import SymmetricSubgroupAsymptotics.BinaryPairSectionCocycleBound

/-!
# The active socle in the four-ternary pair rows

This file supplies the two representation-theoretic inputs left abstract by
`PrimitiveAffineDegreeTwoFourTernaryBlocks`.  The first identifies the active
minimal normal factors with those carried by the retained four-plane image.
The second realizes every such factor in the exact binary pair section and
uses the surviving ternary core to force at least sixteen elements.
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

/-! ## The active commutator criterion -/

/-- An ambient-minimal subgroup carried by the surviving four-plane image
cannot be centralized by the retained ternary image.  A hypothetical
central factor supplies a nonzero four-plane vector fixed modulo the literal
normal axis by the whole displayed ternary core, contradicting the common
Maschke descent from the fixed-socle analysis. -/
theorem minimalNormal_retainedAveragingImage_is_active
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p)
    (N : LiteralNormalAxis (p := p))
    (M : Subgroup (preE7PairAction 12 p ⧸ N.1))
    (hM : IsMinimalNormalSubgroup M)
    (hME : M ≤ S.retainedAveragingImage R N) :
    ⁅S.retainedTernaryImage R N, M⁆ = M := by
  letI : M.Normal := hM.1
  rcases minimalNormal_commutator_full_or_trivial
      (S.retainedTernaryImage R N) M hM with hfull | hcommBot
  · exact hfull
  · exfalso
    obtain ⟨m, hmne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hM.2.1
    obtain ⟨u, huA, hu⟩ := hME m.2
    have hutop : R.frame.top u = 1 :=
      R.frame.coordinateSubgroup_le_kernel
        (S.averagingCoordinateRepresentation R).toSubmodule huA
    let ku : R.frame.top.ker := ⟨u, hutop⟩
    have hvA : R.frame.bits ku ∈ S.augmentationPlanes := by
      exact ((R.frame.kernel_mem_coordinateSubgroup
        (S.averagingCoordinateRepresentation R).toSubmodule ku).1 huA).1
    let v : S.augmentationPlanes := ⟨R.frame.bits ku, hvA⟩
    let I : Subrepresentation
        (S.augmentationNormalCoreRepresentation S.core) :=
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
      have huN : u ∈ N.1 :=
        (R.frame.bits_mem_ambientAxis N.1 ku).mp hv
      apply hmne
      apply Subtype.ext
      rw [← hu]
      exact (QuotientGroup.eq_one_iff u).2 huN
    have hcoreNe : S.core ≠ ⊥ := by
      intro hbot
      have hcard := S.core_card_lower
      rw [hbot] at hcard
      norm_num at hcard
    apply S.augmentationPlanes_no_fixed_vector_mod_normalCoreSubgroup
      S.core le_rfl hcoreNe I v hvI
    intro k
    obtain ⟨g, hgTop⟩ := S.realizedTop_surjective R k.1
    have hqgT : QuotientGroup.mk' N.1 g ∈
        S.retainedTernaryImage R N := by
      refine ⟨g, ?_, rfl⟩
      change S.realizedTop R g ∈ S.core
      rw [hgTop]
      exact k.2
    have hMC : M ≤ Subgroup.centralizer
        (S.retainedTernaryImage R N :
          Set (preE7PairAction 12 p ⧸ N.1)) := by
      rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
      simpa only [Subgroup.commutator_comm] using hcommBot
    have hcomm : Commute (QuotientGroup.mk' N.1 g)
        (QuotientGroup.mk' N.1 u) := by
      rw [hu]
      exact Subgroup.mem_centralizer_iff.mp (hMC m.2) _ hqgT
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

/-- The active commutator condition is exactly survival inside the retained
four-plane image for ambient-minimal normal subgroups. -/
theorem minimalNormal_active_iff_le_retainedAveragingImage
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p)
    (N : LiteralNormalAxis (p := p))
    (M : Subgroup (preE7PairAction 12 p ⧸ N.1))
    (hM : IsMinimalNormalSubgroup M) :
    (⁅S.retainedTernaryImage R N, M⁆ = M ↔
      M ≤ S.retainedAveragingImage R N) := by
  constructor
  · exact S.minimalNormal_active_le_retainedAveragingImage R N M
  · exact S.minimalNormal_retainedAveragingImage_is_active R N M hM

/-! ## Exact binary coordinates of one retained minimal factor -/

/-- Pull a retained subgroup back to the literal pair kernel. -/
def activePairPreimage
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p)
    (N : LiteralNormalAxis (p := p))
    (M : Subgroup (preE7PairAction 12 p ⧸ N.1)) :
    Subgroup R.frame.top.ker :=
  (M.comap (QuotientGroup.mk' N.1)).subgroupOf R.frame.top.ker

theorem normalSubgroupOfPairKernel_le_activePairPreimage
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p)
    (N : LiteralNormalAxis (p := p))
    (M : Subgroup (preE7PairAction 12 p ⧸ N.1)) :
    N.1.subgroupOf R.frame.top.ker ≤ S.activePairPreimage R N M := by
  intro k hk
  change QuotientGroup.mk' N.1 (k.1 : preE7PairAction 12 p) ∈ M
  have hq : QuotientGroup.mk' N.1
      (k.1 : preE7PairAction 12 p) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hk
  rw [hq]
  exact Subgroup.one_mem M

/-- Exact binary section occupied by one retained subgroup. -/
def activePairSpace
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p)
    (N : LiteralNormalAxis (p := p))
    (M : Subgroup (preE7PairAction 12 p ⧸ N.1)) :
    Submodule (ZMod 2)
      (R.frame.kernelSpace ⧸ R.frame.normalSpace N.1) :=
  sectionSubgroupImage (p := 2) (R.frame.sectionMap N.1)
    (S.activePairPreimage R N M)

/-- Realization of the pulled-back pair-kernel quotient inside the retained
group. -/
def activePairIntersectionMap
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p)
    (N : LiteralNormalAxis (p := p))
    (M : Subgroup (preE7PairAction 12 p ⧸ N.1)) :
    S.activePairPreimage R N M →*
      ((M ⊓ S.retainedPairKernel R N) :
        Subgroup (preE7PairAction 12 p ⧸ N.1)) where
  toFun k := ⟨QuotientGroup.mk' N.1
    (k.1 : preE7PairAction 12 p), k.2, ⟨k.1, k.1.2, rfl⟩⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (QuotientGroup.mk' N.1)
  map_mul' k l := by
    apply Subtype.ext
    exact map_mul (QuotientGroup.mk' N.1)
      (k.1 : preE7PairAction 12 p) l.1

theorem activePairIntersectionMap_surjective
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p)
    (N : LiteralNormalAxis (p := p))
    (M : Subgroup (preE7PairAction 12 p ⧸ N.1)) :
    Function.Surjective (S.activePairIntersectionMap R N M) := by
  rintro ⟨x, hxM, hxE⟩
  obtain ⟨k, hk, rfl⟩ := hxE
  let kK : R.frame.top.ker := ⟨k, hk⟩
  have hkL : kK ∈ S.activePairPreimage R N M := hxM
  exact ⟨⟨kK, hkL⟩, rfl⟩

/-- The same quotient represented by vectors in the exact pair section. -/
def activePairSpaceMap
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p)
    (N : LiteralNormalAxis (p := p))
    (M : Subgroup (preE7PairAction 12 p ⧸ N.1)) :
    S.activePairPreimage R N M →*
      Multiplicative (S.activePairSpace R N M) where
  toFun k := Multiplicative.ofAdd
    ⟨(R.frame.sectionMap N.1 k.1).toAdd,
      (sectionSubgroupImage_mem_iff (p := 2)
        (R.frame.sectionMap N.1) (S.activePairPreimage R N M)
        (by
          rw [R.frame.sectionMap_ker]
          exact S.normalSubgroupOfPairKernel_le_activePairPreimage R N M)
        k.1).2 k.2⟩
  map_one' := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd
      (map_one (R.frame.sectionMap N.1))
  map_mul' k l := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd
      (map_mul (R.frame.sectionMap N.1) k.1 l.1)

theorem activePairSpaceMap_surjective
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p)
    (N : LiteralNormalAxis (p := p))
    (M : Subgroup (preE7PairAction 12 p ⧸ N.1)) :
    Function.Surjective (S.activePairSpaceMap R N M) := by
  intro v
  obtain ⟨k, hk⟩ := R.frame.sectionMap_surjective N.1
    (Multiplicative.ofAdd v.1)
  have hkL : k ∈ S.activePairPreimage R N M :=
    (sectionSubgroupImage_mem_iff (p := 2)
      (R.frame.sectionMap N.1) (S.activePairPreimage R N M)
      (by
        rw [R.frame.sectionMap_ker]
        exact S.normalSubgroupOfPairKernel_le_activePairPreimage R N M)
      k).1 (by
        rw [hk]
        exact v.2)
  refine ⟨⟨k, hkL⟩, ?_⟩
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  exact congrArg Multiplicative.toAdd hk

theorem activePairIntersectionMap_ker_eq_activePairSpaceMap_ker
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p)
    (N : LiteralNormalAxis (p := p))
    (M : Subgroup (preE7PairAction 12 p ⧸ N.1)) :
    (S.activePairIntersectionMap R N M).ker =
      (S.activePairSpaceMap R N M).ker := by
  ext k
  constructor
  · intro hk
    have hq : QuotientGroup.mk' N.1
        (k.1 : preE7PairAction 12 p) = 1 :=
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
      (fun z : Multiplicative (S.activePairSpace R N M) ↦ z.toAdd.1)
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

/-- Cardinal transport through the same literal pair section used in the
fixed-socle argument. -/
theorem activePairIntersection_card_eq_activePairSpace
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p)
    (N : LiteralNormalAxis (p := p))
    (M : Subgroup (preE7PairAction 12 p ⧸ N.1)) :
    Nat.card ((M ⊓ S.retainedPairKernel R N) :
        Subgroup (preE7PairAction 12 p ⧸ N.1)) =
      Nat.card (S.activePairSpace R N M) := by
  let e := surjectiveTargetEquivOfKernelEq
    (S.activePairIntersectionMap R N M) (S.activePairSpaceMap R N M)
    (S.activePairIntersectionMap_surjective R N M)
    (S.activePairSpaceMap_surjective R N M)
    (S.activePairIntersectionMap_ker_eq_activePairSpaceMap_ker R N M)
  exact (Nat.card_congr e.toEquiv).trans
    (Nat.card_congr Multiplicative.toAdd)

theorem activePairSpace_card_eq_of_le_retainedAveragingImage
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p)
    (N : LiteralNormalAxis (p := p))
    (M : Subgroup (preE7PairAction 12 p ⧸ N.1))
    (hME : M ≤ S.retainedAveragingImage R N) :
    Nat.card M = Nat.card (S.activePairSpace R N M) := by
  have hMP : M ≤ S.retainedPairKernel R N :=
    hME.trans (S.retainedAveragingImage_le_retainedPairKernel R N)
  simpa only [inf_eq_left.mpr hMP] using
    S.activePairIntersection_card_eq_activePairSpace R N M

/-! ## The surviving ternary-core action -/

/-- Action of the literal degree-twelve top on the exact pair section. -/
def topPairSectionRepresentation
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p)
    (N : LiteralNormalAxis (p := p)) :
    Representation (ZMod 2) D.top
      (R.frame.kernelSpace ⧸ R.frame.normalSpace N.1) :=
  (R.frame.sectionRepresentation N.1).comp
    ((R.frame.sectionTopQuotient N.1).comp R.topEquiv.toMonoidHom)

theorem activePairPreimage_conj
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p)
    (N : LiteralNormalAxis (p := p))
    (M : Subgroup (preE7PairAction 12 p ⧸ N.1)) [M.Normal]
    (g : preE7PairAction 12 p) (k : R.frame.top.ker)
    (hk : k ∈ S.activePairPreimage R N M) :
    MulAut.conjNormal g k ∈ S.activePairPreimage R N M := by
  change QuotientGroup.mk' N.1
      ((MulAut.conjNormal g k : R.frame.top.ker) :
        preE7PairAction 12 p) ∈ M
  change QuotientGroup.mk' N.1
      (g * (k : preE7PairAction 12 p) * g⁻¹) ∈ M
  simp only [map_mul, map_inv]
  exact Subgroup.Normal.conj_mem inferInstance
    (QuotientGroup.mk' N.1 (k : preE7PairAction 12 p)) hk
    (QuotientGroup.mk' N.1 g)

/-- The exact active binary subspace is stable under the entire literal
degree-twelve top, because it is pulled back from an ambient normal
subgroup. -/
def activePairSubrepresentation
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p)
    (N : LiteralNormalAxis (p := p))
    (M : Subgroup (preE7PairAction 12 p ⧸ N.1)) [M.Normal] :
    Subrepresentation (S.topPairSectionRepresentation R N) where
  toSubmodule := S.activePairSpace R N M
  apply_mem_toSubmodule := by
    intro t w hw
    obtain ⟨k, hk⟩ := R.frame.sectionMap_surjective N.1
      (Multiplicative.ofAdd w)
    have hkw : (R.frame.sectionMap N.1 k).toAdd = w :=
      congrArg Multiplicative.toAdd hk
    have hkM : k ∈ S.activePairPreimage R N M :=
      (sectionSubgroupImage_mem_iff (p := 2)
        (R.frame.sectionMap N.1) (S.activePairPreimage R N M)
        (by
          rw [R.frame.sectionMap_ker]
          exact S.normalSubgroupOfPairKernel_le_activePairPreimage R N M)
        k).1 (by
          rw [hkw]
          exact hw)
    obtain ⟨g, hg⟩ :=
      R.frame.top.rangeRestrict_surjective (R.topEquiv t)
    have hconj := S.activePairPreimage_conj R N M g k hkM
    have hconjImage :
        (R.frame.sectionMap N.1 (MulAut.conjNormal g k)).toAdd ∈
          S.activePairSpace R N M :=
      (sectionSubgroupImage_mem_iff (p := 2)
        (R.frame.sectionMap N.1) (S.activePairPreimage R N M)
        (by
          rw [R.frame.sectionMap_ker]
          exact S.normalSubgroupOfPairKernel_le_activePairPreimage R N M)
        (MulAut.conjNormal g k)).2 hconj
    change R.frame.sectionRepresentation N.1
        (R.frame.sectionTopQuotient N.1 (R.topEquiv t)) w ∈
      S.activePairSpace R N M
    rw [← hkw]
    rw [← hg, R.frame.sectionTopQuotient_apply,
      R.frame.sectionRepresentation_apply]
    exact hconjImage

/-- The representation of the full top on the retained minimal-factor
subspace. -/
def topActivePairRepresentation
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p)
    (N : LiteralNormalAxis (p := p))
    (M : Subgroup (preE7PairAction 12 p ⧸ N.1)) [M.Normal] :
    Representation (ZMod 2) D.top (S.activePairSpace R N M) :=
  (S.activePairSubrepresentation R N M).toRepresentation

/-- The vector in the exact active subspace represented by one literal
pair-kernel lift. -/
def activePairVector
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p)
    (N : LiteralNormalAxis (p := p))
    (M : Subgroup (preE7PairAction 12 p ⧸ N.1))
    (k : R.frame.top.ker) (hk : k ∈ S.activePairPreimage R N M) :
    S.activePairSpace R N M :=
  ⟨(R.frame.sectionMap N.1 k).toAdd,
    (sectionSubgroupImage_mem_iff (p := 2)
      (R.frame.sectionMap N.1) (S.activePairPreimage R N M)
      (by
        rw [R.frame.sectionMap_ker]
        exact S.normalSubgroupOfPairKernel_le_activePairPreimage R N M)
      k).2 hk⟩

@[simp] theorem topActivePairRepresentation_apply_activePairVector
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p)
    (N : LiteralNormalAxis (p := p))
    (M : Subgroup (preE7PairAction 12 p ⧸ N.1)) [M.Normal]
    (g : preE7PairAction 12 p) (k : R.frame.top.ker)
    (hk : k ∈ S.activePairPreimage R N M) :
    S.topActivePairRepresentation R N M (S.realizedTop R g)
        (S.activePairVector R N M k hk) =
      S.activePairVector R N M (MulAut.conjNormal g k)
        (S.activePairPreimage_conj R N M g k hk) := by
  apply Subtype.ext
  change R.frame.sectionRepresentation N.1
      (R.frame.sectionTopQuotient N.1
        (R.topEquiv (S.realizedTop R g)))
      (R.frame.sectionMap N.1 k).toAdd =
        (R.frame.sectionMap N.1 (MulAut.conjNormal g k)).toAdd
  have htop : R.topEquiv (S.realizedTop R g) =
      R.frame.top.rangeRestrict g := by
    exact R.topEquiv.apply_symm_apply (R.frame.top.rangeRestrict g)
  rw [htop]
  rw [R.frame.sectionTopQuotient_apply,
    R.frame.sectionRepresentation_apply]

/-- Restriction of the retained minimal-factor section to the displayed
ternary core. -/
def activePairRepresentation
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p)
    (N : LiteralNormalAxis (p := p))
    (M : Subgroup (preE7PairAction 12 p ⧸ N.1)) [M.Normal] :
    Representation (ZMod 2) S.core (S.activePairSpace R N M) :=
  (S.topActivePairRepresentation R N M).comp S.core.subtype

/-- Kernel of the full top action on one retained active section, cut back
to the displayed ternary core.  It is normal in the full top. -/
def activeCoreKernel
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p)
    (N : LiteralNormalAxis (p := p))
    (M : Subgroup (preE7PairAction 12 p ⧸ N.1)) [M.Normal] :
    Subgroup D.top :=
  (S.topActivePairRepresentation R N M).ker ⊓ S.core

noncomputable instance activeCoreKernel_normal
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p)
    (N : LiteralNormalAxis (p := p))
    (M : Subgroup (preE7PairAction 12 p ⧸ N.1)) [M.Normal] :
    (S.activeCoreKernel R N M).Normal := inferInstance

/-- The surviving ternary core acts faithfully on every ambient-minimal
factor carried by the retained four-plane image.  A nonzero kernel would be
a full-top-normal subgroup inside the core.  The same literal lift used to
represent a nonidentity element of `M` would then be fixed modulo `N`,
contradicting the no-fixed-vector theorem for the four augmentation planes. -/
theorem activeCoreKernel_eq_bot
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p)
    (N : LiteralNormalAxis (p := p))
    (M : Subgroup (preE7PairAction 12 p ⧸ N.1))
    (hM : IsMinimalNormalSubgroup M)
    (hME : M ≤ S.retainedAveragingImage R N) :
    S.activeCoreKernel R N M = ⊥ := by
  letI : M.Normal := hM.1
  by_contra hK
  let K : Subgroup D.top := S.activeCoreKernel R N M
  letI : K.Normal := inferInstance
  have hKC : K ≤ S.core := inf_le_right
  have hKne : K ≠ ⊥ := by
    simpa only [K] using hK
  obtain ⟨m, hmne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hM.2.1
  obtain ⟨u, huA, hu⟩ := hME m.2
  have hutop : R.frame.top u = 1 :=
    R.frame.coordinateSubgroup_le_kernel
      (S.averagingCoordinateRepresentation R).toSubmodule huA
  let ku : R.frame.top.ker := ⟨u, hutop⟩
  have hquM : QuotientGroup.mk' N.1 u ∈ M := by
    rw [hu]
    exact m.2
  have hkuM : ku ∈ S.activePairPreimage R N M := hquM
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
    have huN : u ∈ N.1 :=
      (R.frame.bits_mem_ambientAxis N.1 ku).mp hv
    apply hmne
    apply Subtype.ext
    rw [← hu]
    exact (QuotientGroup.eq_one_iff u).2 huN
  apply S.augmentationPlanes_no_fixed_vector_mod_normalCoreSubgroup
    K hKC hKne I v hvI
  intro k
  obtain ⟨g, hgTop⟩ := S.realizedTop_surjective R k.1
  let w : S.activePairSpace R N M :=
    S.activePairVector R N M ku hkuM
  have hrepOne : S.topActivePairRepresentation R N M k.1 = 1 :=
    MonoidHom.mem_ker.mp k.2.1
  have hwfix :
      S.topActivePairRepresentation R N M (S.realizedTop R g) w = w := by
    rw [hgTop, hrepOne]
    rfl
  have hwaction :=
    S.topActivePairRepresentation_apply_activePairVector
      R N M g ku hkuM
  have hsAdd :
      (R.frame.sectionMap N.1 (MulAut.conjNormal g ku)).toAdd =
        (R.frame.sectionMap N.1 ku).toAdd := by
    exact congrArg Subtype.val (hwaction.symm.trans hwfix)
  have hs : R.frame.sectionMap N.1 (MulAut.conjNormal g ku) =
      R.frame.sectionMap N.1 ku := by
    apply Multiplicative.toAdd.injective
    exact hsAdd
  let d : R.frame.top.ker := ku⁻¹ * MulAut.conjNormal g ku
  have hdN : (d : preE7PairAction 12 p) ∈ N.1 := by
    change d ∈ N.1.subgroupOf R.frame.top.ker
    rw [← R.frame.sectionMap_ker]
    apply MonoidHom.mem_ker.mpr
    change R.frame.sectionMap N.1 ku⁻¹ *
      R.frame.sectionMap N.1 (MulAut.conjNormal g ku) = 1
    rw [map_inv, hs, inv_mul]
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

theorem activePairRepresentation_injective
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p)
    (N : LiteralNormalAxis (p := p))
    (M : Subgroup (preE7PairAction 12 p ⧸ N.1))
    (hM : IsMinimalNormalSubgroup M)
    (hME : M ≤ S.retainedAveragingImage R N) :
    Function.Injective (S.activePairRepresentation R N M) := by
  letI : M.Normal := hM.1
  have hK := S.activeCoreKernel_eq_bot R N M hM hME
  rw [injective_iff_map_eq_one]
  intro c hc
  have hcK : (c.1 : D.top) ∈ S.activeCoreKernel R N M := by
    refine ⟨?_, c.2⟩
    apply MonoidHom.mem_ker.mpr
    change S.topActivePairRepresentation R N M c.1 = 1
    change S.topActivePairRepresentation R N M c.1 = 1 at hc
    exact hc
  have hcbot : (c.1 : D.top) ∈ (⊥ : Subgroup D.top) := by
    rw [← hK]
    exact hcK
  apply Subtype.ext
  exact Subgroup.mem_bot.mp hcbot

/-- Every ambient-minimal factor in the retained four-plane image has at
least sixteen elements. -/
theorem sixteen_le_card_minimalNormal_of_le_retainedAveragingImage
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p)
    (N : LiteralNormalAxis (p := p))
    (M : Subgroup (preE7PairAction 12 p ⧸ N.1))
    (hM : IsMinimalNormalSubgroup M)
    (hME : M ≤ S.retainedAveragingImage R N) :
    16 ≤ Nat.card M := by
  letI : M.Normal := hM.1
  rw [S.activePairSpace_card_eq_of_le_retainedAveragingImage R N M hME]
  exact S.sixteen_le_card_of_nine_le_exponent_three_faithful_representation
    S.core_commutative S.core_exponent_three S.core_card_lower
    (S.activePairRepresentation R N M)
    (S.activePairRepresentation_injective R N M hM hME)

/-! ## The unconditional active and whole-socle bounds -/

theorem retainedActiveSocle_normalGen_le_two
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p)
    (N : LiteralNormalAxis (p := p)) :
    MarkedC4.normalGen
      (nontrivialActionSoclePart (preE7PairAction 12 p ⧸ N.1)
        (S.retainedTernaryImage R N)) ≤ 2 := by
  apply S.retainedActiveSocle_normalGen_le_two_of_faithfulSections R N
  · intro M hM
    exact S.minimalNormal_active_iff_le_retainedAveragingImage R N M hM
  · intro M hM hME
    exact S.sixteen_le_card_minimalNormal_of_le_retainedAveragingImage
      R N M hM hME

theorem retainedSoclePartsBounds_active :
    ∀ (p : PreE7PairActionClass 12)
      (R : DegreeTwoPairTopRealization D p)
      (N : LiteralNormalAxis (p := p)),
      ¬ S.averagingSubgroup R ≤ N.1 →
        MarkedC4.normalGen
          (nontrivialActionSoclePart (preE7PairAction 12 p ⧸ N.1)
            (S.retainedTernaryImage R N)) ≤ 2 := by
  intro p R N _hN
  exact S.retainedActiveSocle_normalGen_le_two R N

/-- Both socle-part estimates, with no remaining row-wise hypothesis. -/
def retainedSoclePartsBounds : S.RetainedSoclePartsBounds where
  active := S.retainedSoclePartsBounds_active
  fixed := S.retainedSoclePartsBounds_fixed

/-- The final retained-socle theorem for all four-ternary top structures. -/
theorem retainedSocleTheorem : S.RetainedSocleTheorem :=
  S.retainedSocleTheorem_of_parts S.retainedSoclePartsBounds

end DegreeTwoFourTernaryTopStructure
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
