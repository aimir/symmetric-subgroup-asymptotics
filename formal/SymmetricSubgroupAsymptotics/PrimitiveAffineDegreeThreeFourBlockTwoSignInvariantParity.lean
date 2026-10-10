import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockTwoSignSectionRank

/-!
# Even rank of every invariant intersection in the two-sign branch

The two literal sign fibres are exchanged by the transitive block top.
Consequently every invariant subrepresentation has equal dimension in its
two repeated-sign components, hence even total dimension.  Applying this
to the exact normal subrepresentation attached to `N ∩ E` closes the
rank-two theorem for every proper ternary section.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

open DiagonalInvariantSubmodules
open DiagonalIsotypeProjection

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

local instance : Fact P.p.Prime := (chart block P).primeFact

private abbrev QuotientRep :
    Representation (ZMod P.p)
      (preE7NonPairAction w U ⧸ E block P)
      (TranslationSubmodule block P) :=
  (elementaryChart block P).quotientRepresentation.ρ

/-- The restricted literal coordinate map on an invariant
subrepresentation. -/
def degreeThreeFourBlockReindexedSubrepresentationMap
    (hs : Nat.card block.Points = 4)
    (W : Subrepresentation (QuotientRep block P)) :
    W.toSubmodule →ₗ[ZMod P.p] (Fin 4 → (chart block P).V) :=
  (degreeThreeFourBlockTranslationCoordinateMap block P hs).domRestrict
    W.toSubmodule

/-- Reindex an invariant subrepresentation into the literal four-coordinate
ambient module. -/
def degreeThreeFourBlockReindexedSubrepresentation
    (hs : Nat.card block.Points = 4)
    (W : Subrepresentation (QuotientRep block P)) :
    Submodule (ZMod P.p) (Fin 4 → (chart block P).V) :=
  LinearMap.range
    (degreeThreeFourBlockReindexedSubrepresentationMap block P hs W)

/-- Exact linear equivalence from an invariant subrepresentation onto its
reindexed coordinate image. -/
noncomputable def degreeThreeFourBlockReindexedSubrepresentationEquiv
    (hs : Nat.card block.Points = 4)
    (W : Subrepresentation (QuotientRep block P)) :
    W.toSubmodule ≃ₗ[ZMod P.p]
      degreeThreeFourBlockReindexedSubrepresentation block P hs W := by
  apply LinearEquiv.ofInjective
    (degreeThreeFourBlockReindexedSubrepresentationMap block P hs W)
  exact (degreeThreeFourBlockTranslationCoordinateMap_injective
    block P hs).comp Subtype.val_injective

@[simp] theorem degreeThreeFourBlockReindexedSubrepresentationEquiv_apply
    (hs : Nat.card block.Points = 4)
    (W : Subrepresentation (QuotientRep block P))
    (x : W.toSubmodule) (i : Fin 4) :
    (degreeThreeFourBlockReindexedSubrepresentationEquiv
      block P hs W x).1 i =
      x.1.1 ((degreeThreeFourBlockIndexEquiv block hs).symm i) := by
  change degreeThreeFourBlockTranslationCoordinateMap block P hs x.1 i = _
  rfl

/-- An invariant subrepresentation remains stable under the literal
diagonal pair-kernel characters after reindexing. -/
noncomputable def degreeThreeFourBlockReindexedSubrepresentationStable
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (W : Subrepresentation (QuotientRep block P)) :
    ModuleStable (V := (chart block P).V)
      (degreeThreeFourBlockTranslationScalar
        block P hr hs hcomponent) := by
  let C := degreeThreeFourBlockPairChart block P hr hs hcomponent
  let e := degreeThreeFourBlockIndexEquiv block hs
  let A := degreeThreeFourBlockSignedTranslationCompatibility
    block P hr hs hcomponent
  refine ⟨degreeThreeFourBlockReindexedSubrepresentation block P hs W, ?_⟩
  intro k y hy
  rcases hy with ⟨x, rfl⟩
  let q := C.sourceEquiv.symm k.1
  let z : W.toSubmodule :=
    ⟨(QuotientRep block P) q x.1,
      W.apply_mem_toSubmodule q x.2⟩
  refine ⟨z, ?_⟩
  simpa only [C, e, A, q, z,
    degreeThreeFourBlockReindexedSubrepresentationMap] using
      A.diagonal_action k x.1

/-- Restrict one quotient-representation automorphism to an invariant
subrepresentation. -/
noncomputable def degreeThreeFourBlockSubrepresentationActionEquiv
    (W : Subrepresentation (QuotientRep block P))
    (q : preE7NonPairAction w U ⧸ E block P) :
    W.toSubmodule ≃ₗ[ZMod P.p] W.toSubmodule where
  toFun x := ⟨(QuotientRep block P) q x.1,
    W.apply_mem_toSubmodule q x.2⟩
  invFun x := ⟨(QuotientRep block P) q⁻¹ x.1,
    W.apply_mem_toSubmodule q⁻¹ x.2⟩
  left_inv x := by
    apply Subtype.ext
    exact (QuotientRep block P).inv_self_apply q x.1
  right_inv x := by
    apply Subtype.ext
    exact (QuotientRep block P).self_inv_apply q x.1
  map_add' x y := by
    apply Subtype.ext
    exact map_add ((QuotientRep block P) q) x.1 y.1
  map_smul' c x := by
    apply Subtype.ext
    exact map_smul ((QuotientRep block P) q) c x.1

/-- The preceding restricted action in reindexed coordinates. -/
noncomputable def degreeThreeFourBlockReindexedSubrepresentationActionEquiv
    (hs : Nat.card block.Points = 4)
    (W : Subrepresentation (QuotientRep block P))
    (q : preE7NonPairAction w U ⧸ E block P) :
    degreeThreeFourBlockReindexedSubrepresentation block P hs W ≃ₗ[ZMod P.p]
      degreeThreeFourBlockReindexedSubrepresentation block P hs W :=
  (degreeThreeFourBlockReindexedSubrepresentationEquiv
      block P hs W).symm.trans
    ((degreeThreeFourBlockSubrepresentationActionEquiv block P W q).trans
      (degreeThreeFourBlockReindexedSubrepresentationEquiv block P hs W))

/-- Restricted quotient conjugation preserves coordinate zeroes exactly
along the literal top permutation. -/
theorem degreeThreeFourBlockReindexedSubrepresentationAction_zero_iff
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (W : Subrepresentation (QuotientRep block P))
    (a : preE7NonPairAction w U)
    (x : degreeThreeFourBlockReindexedSubrepresentation block P hs W)
    (i : Fin 4) :
    let q := QuotientGroup.mk' (E block P) a
    let C := degreeThreeFourBlockPairChart block P hr hs hcomponent
    (degreeThreeFourBlockReindexedSubrepresentationActionEquiv
      block P hs W q x).1 (C.frame.top (C.sourceEquiv q) i) = 0 ↔
      x.1 i = 0 := by
  let q := QuotientGroup.mk' (E block P) a
  let C := degreeThreeFourBlockPairChart block P hr hs hcomponent
  dsimp only
  let idx := degreeThreeFourBlockIndexEquiv block hs
  let v : W.toSubmodule :=
    (degreeThreeFourBlockReindexedSubrepresentationEquiv
      block P hs W).symm x
  let L := (binaryAffineLocalLinearRepresentation block P).ρ
    (localMap block P
      ((ambientEmbedding block a).left
        ((ambientEmbedding block a).right • idx.symm i)))
  have htop := degreeThreeFourBlockPairChart_top_apply
    block P hr hs hcomponent q (idx.symm i)
  have htop' : C.frame.top (C.sourceEquiv q) i =
      idx ((ambientEmbedding block a).right • idx.symm i) := by
    simpa only [q, C, idx, idx.apply_symm_apply] using htop
  have hv : v.1.1 (idx.symm i) = x.1 i := by
    have h := degreeThreeFourBlockReindexedSubrepresentationEquiv_apply
      block P hs W v i
    rw [(degreeThreeFourBlockReindexedSubrepresentationEquiv
      block P hs W).apply_symm_apply x] at h
    exact h.symm
  have htransport :=
    translationSubmodule_quotientRepresentation_coordinate_transport
      block P a v.1 (idx.symm i)
  have hcoordinate :
      (degreeThreeFourBlockReindexedSubrepresentationActionEquiv
        block P hs W q x).1 (C.frame.top (C.sourceEquiv q) i) =
        L (v.1.1 (idx.symm i)) := by
    rw [htop']
    change (degreeThreeFourBlockReindexedSubrepresentationEquiv
      block P hs W
        (degreeThreeFourBlockSubrepresentationActionEquiv
          block P W q v)).1
          (idx ((ambientEmbedding block a).right • idx.symm i)) = _
    rw [degreeThreeFourBlockReindexedSubrepresentationEquiv_apply,
      idx.symm_apply_apply]
    change (((QuotientRep block P) q v.1).1
        ((ambientEmbedding block a).right • idx.symm i)) = _
    simpa only [q, L] using htransport
  rw [hcoordinate, hv]
  constructor
  · intro hzero
    apply ((binaryAffineLocalLinearRepresentation block P).ρ.apply_bijective
      (localMap block P
        ((ambientEmbedding block a).left
          ((ambientEmbedding block a).right • idx.symm i)))).injective
    simpa only [map_zero] using hzero
  · intro hzero
    rw [hzero, map_zero]

/-- The scalarized repeated-sign pieces of every invariant
subrepresentation are equidimensional. -/
theorem degreeThreeFourBlockTwoSign_subrepresentation_components_equidimensional
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (W : Subrepresentation (QuotientRep block P))
    (e : (chart block P).V ≃ₗ[ZMod P.p] ZMod P.p)
    (a b : Label (degreeThreeFourBlockTranslationScalar
      block P hr hs hcomponent)) :
    Module.finrank (ZMod P.p)
        (encode (degreeThreeFourBlockTranslationScalar
            block P hr hs hcomponent)
          (scalarizedStable
            (degreeThreeFourBlockTranslationScalar
              block P hr hs hcomponent)
            (degreeThreeFourBlockReindexedSubrepresentationStable
              block P hr hs hcomponent W) e) a) =
      Module.finrank (ZMod P.p)
        (encode (degreeThreeFourBlockTranslationScalar
            block P hr hs hcomponent)
          (scalarizedStable
            (degreeThreeFourBlockTranslationScalar
              block P hr hs hcomponent)
            (degreeThreeFourBlockReindexedSubrepresentationStable
              block P hr hs hcomponent W) e) b) := by
  let C := degreeThreeFourBlockPairChart block P hr hs hcomponent
  let idx := degreeThreeFourBlockIndexEquiv block hs
  let scalar := degreeThreeFourBlockTranslationScalar
    block P hr hs hcomponent
  let K := degreeThreeFourBlockReindexedSubrepresentation block P hs W
  let stableK := degreeThreeFourBlockReindexedSubrepresentationStable
    block P hr hs hcomponent W
  let i := Classical.choose a.2
  let j := Classical.choose b.2
  have hai : scalar i = a.1 := Classical.choose_spec a.2
  have hbj : scalar j = b.1 := Classical.choose_spec b.2
  letI : MulAction.IsPretransitive block.Top block.Points :=
    block.top_pretransitive
  obtain ⟨t, ht⟩ := MulAction.exists_smul_eq block.Top (idx.symm i) (idx.symm j)
  obtain ⟨g, hg⟩ := block.topMap.rangeRestrict_surjective t
  have hright : (ambientEmbedding block g).right • idx.symm i = idx.symm j := by
    change block.topMap.rangeRestrict g • idx.symm i = idx.symm j
    rw [hg]
    exact ht
  let q := QuotientGroup.mk' (E block P) g
  let sigma : Equiv.Perm (Fin 4) := C.frame.top (C.sourceEquiv q)
  have hsigma : sigma i = j := by
    have htop := degreeThreeFourBlockPairChart_top_apply
      block P hr hs hcomponent q (idx.symm i)
    have hqright : (quotientEmbedding block P q).right =
        (ambientEmbedding block g).right := rfl
    change C.frame.top (C.sourceEquiv q) i = j
    rw [show i = idx (idx.symm i) by simp, htop, hqright, hright]
    exact idx.apply_symm_apply j
  let T : K ≃ₗ[ZMod P.p] K :=
    degreeThreeFourBlockReindexedSubrepresentationActionEquiv
      block P hs W q
  have hlabel : ∀ l, scalar (sigma l) = b.1 ↔ scalar l = a.1 := by
    intro l
    have hsi : scalar (sigma i) = b.1 := by
      rw [hsigma]
      exact hbj
    constructor
    · intro hl
      have htop : scalar (sigma l) = scalar (sigma i) := hl.trans hsi.symm
      exact ((degreeThreeFourBlockTranslationScalar_top_eq_iff
        block P hr hs hcomponent (C.sourceEquiv q) l i).1 htop).trans hai
    · intro hl
      have hbase : scalar l = scalar i := hl.trans hai.symm
      exact ((degreeThreeFourBlockTranslationScalar_top_eq_iff
        block P hr hs hcomponent (C.sourceEquiv q) l i).2 hbase).trans hsi
  have hzero : ∀ (x : K) (l : Fin 4),
      (T x).1 (sigma l) = 0 ↔ x.1 l = 0 := by
    intro x l
    exact degreeThreeFourBlockReindexedSubrepresentationAction_zero_iff
      block P hr hs hcomponent W g x l
  have hmodule : Module.finrank (ZMod P.p)
        (ModuleEncode scalar K a) =
      Module.finrank (ZMod P.p) (ModuleEncode scalar K b) :=
    moduleEncode_finrank_eq_of_coordinate_transport
      scalar K a b sigma T hlabel hzero
  rw [← moduleEncode_finrank_eq_scalarized scalar stableK e a,
    ← moduleEncode_finrank_eq_scalarized scalar stableK e b]
  simpa only [stableK,
    degreeThreeFourBlockReindexedSubrepresentationStable, K] using hmodule

/-- Every invariant subrepresentation of the literal two-sign translation
module has even rank. -/
theorem degreeThreeFourBlockTwoSign_subrepresentation_finrank_even
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (W : Subrepresentation (QuotientRep block P)) :
    Even (Module.finrank (ZMod P.p) W.toSubmodule) := by
  let scalar := degreeThreeFourBlockTranslationScalar
    block P hr hs hcomponent
  let K := degreeThreeFourBlockReindexedSubrepresentationStable
    block P hr hs hcomponent W
  have hlocal : Module.finrank (ZMod P.p) (chart block P).V = 1 := by
    have h := (degreeThree_translation_prime_dim block P hr).2
    change Module.finrank (ZMod P.p) (chart block P).V = 1 at h
    exact h
  let e : (chart block P).V ≃ₗ[ZMod P.p] ZMod P.p :=
    LinearEquiv.ofFinrankEq _ _ (by
      rw [hlocal, Module.finrank_self])
  have heven := moduleStable_finrank_even_of_two_equal_isotypes
    scalar K e
    (degreeThreeFourBlockTranslationScalarLabel_card_two
      block P hr hs hcomponent htwo)
    (degreeThreeFourBlockTwoSign_subrepresentation_components_equidimensional
      block P hr hs hcomponent W e)
  have hreindex :=
    (degreeThreeFourBlockReindexedSubrepresentationEquiv
      block P hs W).finrank_eq
  obtain ⟨d, hd⟩ := heven
  exact ⟨d, hreindex.trans hd⟩

/-- The invariant normal-space parity required by the proper-section rank
lemma follows from literal normality, with no extra hypothesis. -/
theorem degreeThreeFourBlockTwoSignSectionNormalSpace_finrank_even
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (N : TwoSignProperAxis (E block P)) :
    Even (Module.finrank (ZMod P.p)
      (degreeThreeFourBlockTwoSignSectionNormalSpace block P N)) := by
  let pi := QuotientGroup.mk' (E block P)
  let rho := (elementaryChart block P).quotientRepresentation
  let chart := (elementaryChart block P).originalKernelChart
  let W : Subrepresentation rho.ρ :=
    chart.normalSubrepresentation pi (QuotientGroup.mk'_surjective (E block P))
      rho (degreeThreeFourBlockTwoSignSectionAxis block P N)
  have h := degreeThreeFourBlockTwoSign_subrepresentation_finrank_even
    block P hr hs hcomponent htwo W
  simpa only [W, OriginalKernelModuleChart.normalSubrepresentation,
    degreeThreeFourBlockTwoSignSectionNormalSpace, pi, rho, chart] using h

/-- Every proper retained two-sign ternary section has rank exactly two. -/
theorem degreeThreeFourBlockTwoSignSectionModule_finrank_eq_two
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (N : TwoSignProperAxis (E block P)) :
    Module.finrank (ZMod P.p)
      (DegreeThreeFourBlockTwoSignSectionModule block P N) = 2 :=
  degreeThreeFourBlockTwoSignSectionModule_finrank_eq_two_of_even_normalSpace
    block P hr hs hcomponent hbinary htwo N
    (degreeThreeFourBlockTwoSignSectionNormalSpace_finrank_even
      block P hr hs hcomponent htwo N)

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
