import SymmetricSubgroupAsymptotics.DiagonalRepeatedIsotypeTransport
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockSignedTranslationCompatibilityTheorem
import SymmetricSubgroupAsymptotics.PrimitiveAffineTranslationSubmoduleCoordinateTransport

/-!
# Literal rank split in the two-sign four-block branch

This file connects the generic repeated-isotype dimension lemmas to the
actual four-block affine translation module.  It records the exact
coordinate equivalence onto the reindexed correlated submodule, identifies
the scalar labels with the original pair-frame sign labels, and transports
the literal block-top action through those labels.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

open OddMarkerTernaryChart
open DiagonalInvariantSubmodules
open DiagonalIsotypeProjection

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

local instance : Fact P.p.Prime := (chart block P).primeFact

/-- Reindexing identifies the actual correlated translation module with
its literal image in four coordinates. -/
noncomputable def degreeThreeFourBlockReindexedTranslationEquiv
    (hs : Nat.card block.Points = 4) :
    TranslationSubmodule block P ≃ₗ[ZMod P.p]
      degreeThreeFourBlockReindexedTranslationSubmodule block P hs := by
  let e := degreeThreeFourBlockIndexEquiv block hs
  let f : TranslationSubmodule block P →ₗ[ZMod P.p]
      degreeThreeFourBlockReindexedTranslationSubmodule block P hs :=
    (((coordinateLinearEquiv (k := ZMod P.p) e).toLinearMap.comp
      (TranslationSubmodule block P).subtype).codRestrict
        (degreeThreeFourBlockReindexedTranslationSubmodule block P hs)
        (fun x ↦ ⟨x.1, x.2, rfl⟩))
  apply LinearEquiv.ofBijective f
  constructor
  · intro x y hxy
    apply Subtype.ext
    apply (coordinateLinearEquiv (k := ZMod P.p) e).injective
    exact congrArg Subtype.val hxy
  · rintro ⟨y, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩

@[simp] theorem degreeThreeFourBlockReindexedTranslationEquiv_apply
    (hs : Nat.card block.Points = 4)
    (x : TranslationSubmodule block P) (i : Fin 4) :
    (degreeThreeFourBlockReindexedTranslationEquiv block P hs x).1 i =
      x.1 ((degreeThreeFourBlockIndexEquiv block hs).symm i) := rfl

/-- The top permutation in the fixed four-pair chart is the reindexed
literal block-top permutation of the original quotient element. -/
theorem degreeThreeFourBlockPairChart_top_apply
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (q : preE7NonPairAction w U ⧸ E block P)
    (j : block.Points) :
    let C := degreeThreeFourBlockPairChart block P hr hs hcomponent
    C.frame.top (C.sourceEquiv q)
        (degreeThreeFourBlockIndexEquiv block hs j) =
      degreeThreeFourBlockIndexEquiv block hs
        ((quotientEmbedding block P q).right • j) := by
  let e : Fin (quotientDegree block) ≃ Fin (2 * 4) := finCongr (by
    rw [quotientDegree_eq block, hr, hs])
  let F₀ := degreeThreeSignedQuotientPairFrame block P hr
  let F₁ := F₀.relabelPoints e
  let idx := degreeThreeFourBlockIndexEquiv block hs
  let C := degreeThreeFourBlockPairChart block P hr hs hcomponent
  change (F₁.reindex idx).top
      (BinaryPairFrame.sourceRelabelEquiv
        (U := (quotientAction block P).range) e
        (degreeThreeSignedQuotientRangeEquiv block P q)) (idx j) =
    idx ((quotientEmbedding block P q).right • j)
  rw [F₁.reindex_top_apply, idx.symm_apply_apply,
    F₀.relabelPoints_top_sourceRelabelEquiv]
  rw [degreeThreeSignedQuotientPairFrame_top_apply]
  change idx (((quotientEmbedding block P q).right :
      Equiv.Perm block.Points) j) =
    idx (((quotientEmbedding block P q).right :
      Equiv.Perm block.Points) j)
  rfl

/-- Equality of the transported ternary scalar characters is exactly
equality of the original binary sign characters. -/
theorem degreeThreeFourBlockTranslationScalar_eq_iff_sign
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (i j : Fin 4) :
    degreeThreeFourBlockTranslationScalar block P hr hs hcomponent i =
        degreeThreeFourBlockTranslationScalar block P hr hs hcomponent j ↔
      BinaryPairFrame.fourCoordinateSign
          (degreeThreeFourBlockPairChart block P hr hs hcomponent).frame i =
        BinaryPairFrame.fourCoordinateSign
          (degreeThreeFourBlockPairChart block P hr hs hcomponent).frame j := by
  let C := degreeThreeFourBlockPairChart block P hr hs hcomponent
  constructor
  · intro h
    apply Subtype.ext
    funext k
    have hk := congrFun h k
    have hsign :
        signScalar (Multiplicative.ofAdd (C.frame.bits k i)) =
          signScalar (Multiplicative.ofAdd (C.frame.bits k j)) := by
      have := congrArg (degreeThreeScalarFieldEquiv block P hr) hk
      simpa only [degreeThreeFourBlockTranslationScalar,
        RingEquiv.apply_symm_apply, C] using this
    exact congrArg Multiplicative.toAdd
      (signScalar_injective hsign)
  · intro h
    funext k
    have hfun := congrArg Subtype.val h
    have hk := congrFun hfun k
    have hk' : C.frame.bits k i = C.frame.bits k j := by
      simpa only [BinaryPairFrame.fourCoordinateSign,
        BinaryPairFrame.fourCoordinateSignFunction, C] using hk
    exact congrArg (degreeThreeScalarFieldEquiv block P hr).symm
      (congrArg (fun z : ZMod 2 ↦ signScalar (Multiplicative.ofAdd z)) hk')

/-- The actual top preserves and reflects equality of transported ternary
scalar labels. -/
theorem degreeThreeFourBlockTranslationScalar_top_eq_iff
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (u : (degreeThreeFourBlockPairChart
      block P hr hs hcomponent).action)
    (i j : Fin 4) :
    degreeThreeFourBlockTranslationScalar block P hr hs hcomponent
          ((degreeThreeFourBlockPairChart
            block P hr hs hcomponent).frame.top u i) =
        degreeThreeFourBlockTranslationScalar block P hr hs hcomponent
          ((degreeThreeFourBlockPairChart
            block P hr hs hcomponent).frame.top u j) ↔
      degreeThreeFourBlockTranslationScalar block P hr hs hcomponent i =
        degreeThreeFourBlockTranslationScalar block P hr hs hcomponent j := by
  let C := degreeThreeFourBlockPairChart block P hr hs hcomponent
  rw [degreeThreeFourBlockTranslationScalar_eq_iff_sign,
    degreeThreeFourBlockTranslationScalar_eq_iff_sign]
  exact BinaryPairFrame.fourCoordinateSign_top_eq_iff C.frame u i j

/-- The transported ternary scalar labels have the same literal finite
cardinality as the pair-frame sign labels. -/
noncomputable def degreeThreeFourBlockTranslationScalarLabelEquiv
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6) :
    Label (degreeThreeFourBlockTranslationScalar
      block P hr hs hcomponent) ≃
      BinaryPairFrame.FourCoordinateSign
        (degreeThreeFourBlockPairChart block P hr hs hcomponent).frame where
  toFun a := BinaryPairFrame.fourCoordinateSign
    (degreeThreeFourBlockPairChart block P hr hs hcomponent).frame
    (Classical.choose a.2)
  invFun a := ⟨degreeThreeFourBlockTranslationScalar
      block P hr hs hcomponent (Classical.choose a.2),
    ⟨Classical.choose a.2, rfl⟩⟩
  left_inv a := by
    apply Subtype.ext
    have hsign₀ := Classical.choose_spec
      ((BinaryPairFrame.fourCoordinateSign
        (degreeThreeFourBlockPairChart block P hr hs hcomponent).frame
        (Classical.choose a.2)).property)
    have hsign :
        BinaryPairFrame.fourCoordinateSign
            (degreeThreeFourBlockPairChart block P hr hs hcomponent).frame
            (Classical.choose
              ((BinaryPairFrame.fourCoordinateSign
                (degreeThreeFourBlockPairChart block P hr hs hcomponent).frame
                (Classical.choose a.2)).property)) =
          BinaryPairFrame.fourCoordinateSign
            (degreeThreeFourBlockPairChart block P hr hs hcomponent).frame
            (Classical.choose a.2) := Subtype.ext hsign₀
    have hscalar :=
      (degreeThreeFourBlockTranslationScalar_eq_iff_sign
        block P hr hs hcomponent _ _).2 hsign
    exact hscalar.trans (Classical.choose_spec a.2)
  right_inv a := by
    apply Subtype.ext
    have hscalar := Classical.choose_spec
      ((⟨degreeThreeFourBlockTranslationScalar
          block P hr hs hcomponent (Classical.choose a.2),
        ⟨Classical.choose a.2, rfl⟩⟩ :
          Label (degreeThreeFourBlockTranslationScalar
            block P hr hs hcomponent)).property)
    have hsign₀ :=
      (degreeThreeFourBlockTranslationScalar_eq_iff_sign
        block P hr hs hcomponent _ _).1 hscalar
    exact congrArg Subtype.val
      (hsign₀.trans (Subtype.ext (Classical.choose_spec a.2)))

/-- In the two-sign branch the transported ternary scalar family has two
labels. -/
theorem degreeThreeFourBlockTranslationScalarLabel_card_two
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2) :
    Nat.card (Label (degreeThreeFourBlockTranslationScalar
      block P hr hs hcomponent)) = 2 := by
  calc
    Nat.card (Label (degreeThreeFourBlockTranslationScalar
        block P hr hs hcomponent)) =
        Nat.card (BinaryPairFrame.FourCoordinateSign
          (degreeThreeFourBlockPairChart block P hr hs hcomponent).frame) :=
      Nat.card_congr
        (degreeThreeFourBlockTranslationScalarLabelEquiv
          block P hr hs hcomponent)
    _ = 2 := by
      simpa only [degreeThreeFourBlockSignedIsotypeProfile,
        BinaryPairFrame.fourCoordinateSignedIsotypeProfile,
        DegreeThreeFourBlockSignedIsotypeProfile.isotypeCount] using htwo

attribute [local instance] Fintype.ofFinite

/-- Every transported ternary scalar label occurs on exactly two of the
four literal coordinates. -/
theorem degreeThreeFourBlockTranslationScalarLabel_fibre_card_two
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (a : Label (degreeThreeFourBlockTranslationScalar
      block P hr hs hcomponent)) :
    Fintype.card (Coordinate
      (degreeThreeFourBlockTranslationScalar block P hr hs hcomponent) a) = 2 := by
  let C := degreeThreeFourBlockPairChart block P hr hs hcomponent
  let i := Classical.choose a.2
  have ha := Classical.choose_spec a.2
  have htwo' : Nat.card (BinaryPairFrame.FourCoordinateSign C.frame) = 2 := by
    simpa only [degreeThreeFourBlockSignedIsotypeProfile,
      BinaryPairFrame.fourCoordinateSignedIsotypeProfile,
      DegreeThreeFourBlockSignedIsotypeProfile.isotypeCount, C] using htwo
  calc
    Fintype.card (Coordinate
        (degreeThreeFourBlockTranslationScalar block P hr hs hcomponent) a) =
        Nat.card {j : Fin 4 //
          BinaryPairFrame.fourCoordinateSign C.frame j =
            BinaryPairFrame.fourCoordinateSign C.frame i} := by
      rw [Fintype.card_eq_nat_card]
      apply Nat.card_congr
      apply Equiv.subtypeEquivRight
      intro j
      constructor
      · intro hj
        apply (degreeThreeFourBlockTranslationScalar_eq_iff_sign
          block P hr hs hcomponent j i).1
        exact hj.trans ha.symm
      · intro hj
        exact ((degreeThreeFourBlockTranslationScalar_eq_iff_sign
          block P hr hs hcomponent j i).2 hj).trans ha
    _ = 2 := by
      let chi := BinaryPairFrame.fourCoordinateSign C.frame i
      let m := Nat.card {j : Fin 4 //
        BinaryPairFrame.fourCoordinateSign C.frame j = chi}
      have hproduct :
          Nat.card (BinaryPairFrame.FourCoordinateSign C.frame) * m = 4 := by
        calc
          Nat.card (BinaryPairFrame.FourCoordinateSign C.frame) * m =
              ∑ _psi : BinaryPairFrame.FourCoordinateSign C.frame, m := by
            simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
              Fintype.card_eq_nat_card, Nat.cast_id]
          _ = ∑ psi : BinaryPairFrame.FourCoordinateSign C.frame,
              Nat.card {j : Fin 4 //
                BinaryPairFrame.fourCoordinateSign C.frame j = psi} := by
            apply Finset.sum_congr rfl
            intro psi _hpsi
            exact (BinaryPairFrame.fourCoordinateSign_fibre_card_eq
              C.frame C.pretransitive psi chi).symm
          _ = Nat.card (Sigma fun psi :
              BinaryPairFrame.FourCoordinateSign C.frame ↦
                {j : Fin 4 //
                  BinaryPairFrame.fourCoordinateSign C.frame j = psi}) :=
            Nat.card_sigma.symm
          _ = Nat.card (Fin 4) :=
            Nat.card_congr
              (Equiv.sigmaFiberEquiv
                (BinaryPairFrame.fourCoordinateSign C.frame))
          _ = 4 := Nat.card_fin 4
      rw [htwo'] at hproduct
      change m = 2
      omega

/-- Quotient conjugation, transported to the literal reindexed correlated
submodule as a linear automorphism. -/
noncomputable def degreeThreeFourBlockReindexedActionEquiv
    (hs : Nat.card block.Points = 4)
    (q : preE7NonPairAction w U ⧸ E block P) :
    degreeThreeFourBlockReindexedTranslationSubmodule block P hs ≃ₗ[ZMod P.p]
      degreeThreeFourBlockReindexedTranslationSubmodule block P hs :=
  let e := degreeThreeFourBlockReindexedTranslationEquiv block P hs
  let r : TranslationSubmodule block P ≃ₗ[ZMod P.p]
      TranslationSubmodule block P :=
    LinearEquiv.ofBijective
      ((elementaryChart block P).quotientRepresentation.ρ q)
      ((elementaryChart block P).quotientRepresentation.ρ.apply_bijective q)
  e.symm.trans (r.trans e)

@[simp] theorem degreeThreeFourBlockReindexedActionEquiv_apply
    (hs : Nat.card block.Points = 4)
    (q : preE7NonPairAction w U ⧸ E block P)
    (x : degreeThreeFourBlockReindexedTranslationSubmodule block P hs) :
    degreeThreeFourBlockReindexedActionEquiv block P hs q x =
      degreeThreeFourBlockReindexedTranslationEquiv block P hs
        ((elementaryChart block P).quotientRepresentation.ρ q
          ((degreeThreeFourBlockReindexedTranslationEquiv
            block P hs).symm x)) := by
  rfl

/-- An actual ambient lift transports coordinate zeroes exactly along the
top permutation in the fixed four-pair chart.  The local factor is an
invertible linear map, so it can neither create nor destroy a zero. -/
theorem degreeThreeFourBlockReindexedAction_zero_iff
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (a : preE7NonPairAction w U)
    (x : degreeThreeFourBlockReindexedTranslationSubmodule block P hs)
    (i : Fin 4) :
    let q := QuotientGroup.mk' (E block P) a
    let C := degreeThreeFourBlockPairChart block P hr hs hcomponent
    (degreeThreeFourBlockReindexedActionEquiv block P hs q x).1
          (C.frame.top (C.sourceEquiv q) i) = 0 ↔
      x.1 i = 0 := by
  let q := QuotientGroup.mk' (E block P) a
  let C := degreeThreeFourBlockPairChart block P hr hs hcomponent
  change (degreeThreeFourBlockReindexedActionEquiv block P hs q x).1
      (C.frame.top (C.sourceEquiv q) i) = 0 ↔ x.1 i = 0
  let idx := degreeThreeFourBlockIndexEquiv block hs
  let v : TranslationSubmodule block P :=
    (degreeThreeFourBlockReindexedTranslationEquiv block P hs).symm x
  let L := (binaryAffineLocalLinearRepresentation block P).ρ
    (localMap block P
      ((ambientEmbedding block a).left
        ((ambientEmbedding block a).right • idx.symm i)))
  have htop := degreeThreeFourBlockPairChart_top_apply
    block P hr hs hcomponent q (idx.symm i)
  have htop' : C.frame.top (C.sourceEquiv q) i =
      idx ((ambientEmbedding block a).right • idx.symm i) := by
    simpa only [q, C, idx, idx.apply_symm_apply] using htop
  have hv : v.1 (idx.symm i) = x.1 i := by
    have h := degreeThreeFourBlockReindexedTranslationEquiv_apply
      block P hs v i
    rw [(degreeThreeFourBlockReindexedTranslationEquiv
      block P hs).apply_symm_apply x] at h
    exact h.symm
  have htransport :=
    translationSubmodule_quotientRepresentation_coordinate_transport
      block P a v (idx.symm i)
  have hcoordinate :
      (degreeThreeFourBlockReindexedActionEquiv block P hs q x).1
          (C.frame.top (C.sourceEquiv q) i) =
        L (v.1 (idx.symm i)) := by
    rw [htop']
    rw [degreeThreeFourBlockReindexedActionEquiv_apply,
      degreeThreeFourBlockReindexedTranslationEquiv_apply,
      idx.symm_apply_apply]
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

/-- Transitivity of the actual block top makes all scalarized repeated-sign
components equidimensional. -/
theorem degreeThreeFourBlockTwoSign_scalarized_components_equidimensional
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (e : (chart block P).V ≃ₗ[ZMod P.p] ZMod P.p)
    (a b : Label (degreeThreeFourBlockTranslationScalar
      block P hr hs hcomponent)) :
    Module.finrank (ZMod P.p)
        (encode (degreeThreeFourBlockTranslationScalar
            block P hr hs hcomponent)
          (scalarizedStable
            (degreeThreeFourBlockTranslationScalar
              block P hr hs hcomponent)
            (DegreeThreeFourBlockSignedTranslationCompatibility.stable
              (block := block) (P := P)
              (degreeThreeFourBlockSignedTranslationCompatibility
                block P hr hs hcomponent)) e) a) =
      Module.finrank (ZMod P.p)
        (encode (degreeThreeFourBlockTranslationScalar
            block P hr hs hcomponent)
          (scalarizedStable
            (degreeThreeFourBlockTranslationScalar
              block P hr hs hcomponent)
            (DegreeThreeFourBlockSignedTranslationCompatibility.stable
              (block := block) (P := P)
              (degreeThreeFourBlockSignedTranslationCompatibility
                block P hr hs hcomponent)) e) b) := by
  let C := degreeThreeFourBlockPairChart block P hr hs hcomponent
  let idx := degreeThreeFourBlockIndexEquiv block hs
  let scalar := degreeThreeFourBlockTranslationScalar
    block P hr hs hcomponent
  let K := degreeThreeFourBlockReindexedTranslationSubmodule block P hs
  let A := degreeThreeFourBlockSignedTranslationCompatibility
    block P hr hs hcomponent
  let stableK := DegreeThreeFourBlockSignedTranslationCompatibility.stable
    (block := block) (P := P) A
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
    degreeThreeFourBlockReindexedActionEquiv block P hs q
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
    exact degreeThreeFourBlockReindexedAction_zero_iff
      block P hr hs hcomponent g x l
  have hmodule : Module.finrank (ZMod P.p)
        (ModuleEncode scalar K a) =
      Module.finrank (ZMod P.p) (ModuleEncode scalar K b) :=
    moduleEncode_finrank_eq_of_coordinate_transport
      scalar K a b sigma T hlabel hzero
  rw [← moduleEncode_finrank_eq_scalarized scalar stableK e a,
    ← moduleEncode_finrank_eq_scalarized scalar stableK e b]
  exact hmodule

/-- The literal two-sign correlated translation module has rank two or
four.  No action catalogue or normal-row census enters the proof. -/
theorem degreeThreeFourBlockTwoSign_translation_finrank_eq_two_or_four
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2) :
    Module.finrank (ZMod P.p) (TranslationSubmodule block P) = 2 ∨
      Module.finrank (ZMod P.p) (TranslationSubmodule block P) = 4 := by
  let scalar := degreeThreeFourBlockTranslationScalar
    block P hr hs hcomponent
  let A := degreeThreeFourBlockSignedTranslationCompatibility
    block P hr hs hcomponent
  let K := DegreeThreeFourBlockSignedTranslationCompatibility.stable
    (block := block) (P := P) A
  have hlocal : Module.finrank (ZMod P.p) (chart block P).V = 1 := by
    have h := (degreeThree_translation_prime_dim block P hr).2
    change Module.finrank (ZMod P.p) (chart block P).V = 1 at h
    exact h
  let e : (chart block P).V ≃ₗ[ZMod P.p] ZMod P.p :=
    LinearEquiv.ofFinrankEq _ _ (by
      rw [hlocal, Module.finrank_self])
  have hfull : ModuleFullCoordinates K.1 :=
    DegreeThreeFourBlockSignedTranslationCompatibility.fullCoordinates
      (block := block) (P := P) hbinary
  have hsplit :=
    moduleStable_finrank_eq_two_or_four_of_two_equal_isotypes
      scalar K e hfull
      (degreeThreeFourBlockTranslationScalarLabel_card_two
        block P hr hs hcomponent htwo)
      (fun a ↦ by
        rw [Fintype.card_eq_nat_card]
        have h := degreeThreeFourBlockTranslationScalarLabel_fibre_card_two
          block P hr hs hcomponent htwo a
        rw [Fintype.card_eq_nat_card] at h
        simpa only [scalar] using h)
      (degreeThreeFourBlockTwoSign_scalarized_components_equidimensional
        block P hr hs hcomponent e)
  have hreindex :=
    (degreeThreeFourBlockReindexedTranslationEquiv block P hs).finrank_eq
  rcases hsplit with htwoRank | hfourRank
  · left
    exact hreindex.trans htwoRank
  · right
    exact hreindex.trans hfourRank

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
