import SymmetricSubgroupAsymptotics.BinaryAffineSmallCatalogueData

/-!
# Consequences of the published small affine catalogue

This file transports the exact representative facts through the published
Roney--Dougal--Unger catalogue locator.  The exported theorems have
the primitive-action hypothesis at the point where it is actually known by
the primitive-affine classifier.  Thus the catalogue is never applied to an
arbitrary regular affine profile which has not been proved primitive.

The degree-`25` composition estimate is deliberately absent: it is proved by
the uniform `GL(2,5)`/`PGL(2,5)` argument rather than by the finite catalogue.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

namespace BinaryAffineSmallCatalogueBridge

private theorem isSolvable_target_of_mulEquiv
    {G R : Type} [Group G] [Group R]
    (e : G ≃* R) (hG : IsSolvable G) : IsSolvable R := by
  letI : IsSolvable G := hG
  exact solvable_of_surjective (f := e.toMonoidHom) e.surjective

private theorem not_isSolvable_target_of_mulEquiv
    {G R : Type} [Group G] [Group R]
    (e : G ≃* R) (hG : ¬ IsSolvable G) : ¬ IsSolvable R := by
  intro hR
  exact hG (isSolvable_target_of_mulEquiv e.symm hR)

private theorem representative_is_soluble_row
    (D : BinaryAffineSmallCatalogueData)
    (r : SmallAffineCatalogueRow)
    (h : IsSolvable (D.representative r).Carrier) :
    r.nonsoluble = false :=
  (D.representativeFacts r).solvable_iff.mp h

private theorem representative_is_nonsoluble_row
    (D : BinaryAffineSmallCatalogueData)
    (r : SmallAffineCatalogueRow)
    (h : ¬ IsSolvable (D.representative r).Carrier) :
    r.nonsoluble = true := by
  cases hr : r.nonsoluble with
  | false => exact (h ((D.representativeFacts r).solvable_iff.mpr hr)).elim
  | true => rfl

/-- Locate a soluble literal point stabilizer in the published small-affine
table, retaining both its exact order and the soluble row flag. -/
theorem locate_soluble
    {G Ω : Type} [Group G] [Finite G] [Fintype Ω]
    [MulAction G Ω] [FaithfulSMul G Ω]
    (D : BinaryAffineSmallCatalogueData)
    (hprimitive : MulAction.IsPreprimitive G Ω)
    (P : PrimitiveAffineProfile G Ω)
    (x : Ω)
    (hdegree : Nat.card Ω = 8 ∨ Nat.card Ω = 16)
    (hsolvable : IsSolvable (P.complement x)) :
    ∃ r : SmallAffineCatalogueRow,
      r.degree = Nat.card Ω ∧ r.nonsoluble = false ∧
      Nat.card (P.complement x) = r.complementOrder := by
  obtain ⟨r, hrDegree, ⟨e⟩⟩ := D.locate hprimitive P x hdegree
  have hrepSolvable : IsSolvable (D.representative r).Carrier :=
    isSolvable_target_of_mulEquiv e hsolvable
  exact ⟨r, hrDegree, representative_is_soluble_row D r hrepSolvable,
    (Nat.card_congr e.toEquiv).trans (D.representativeFacts r).card_eq⟩

/-- A soluble point stabilizer in a literal primitive affine action of
degree eight has order dividing `21`. -/
theorem degreeEight_soluble_card_dvd_twentyOne
    {G Ω : Type} [Group G] [Finite G] [Fintype Ω]
    [MulAction G Ω] [FaithfulSMul G Ω]
    (D : BinaryAffineSmallCatalogueData)
    (hprimitive : MulAction.IsPreprimitive G Ω)
    (P : PrimitiveAffineProfile G Ω)
    (x : Ω) (hdegree : Nat.card Ω = 8)
    (hsolvable : IsSolvable (P.complement x)) :
    Nat.card (P.complement x) ∣ 21 := by
  obtain ⟨r, hrDegree, ⟨e⟩⟩ := D.locate hprimitive P x
    (Or.inl hdegree)
  have hrepSolvable : IsSolvable (D.representative r).Carrier :=
    isSolvable_target_of_mulEquiv e hsolvable
  have hrSoluble : r.nonsoluble = false :=
    representative_is_soluble_row D r hrepSolvable
  rw [Nat.card_congr e.toEquiv, (D.representativeFacts r).card_eq]
  exact SmallAffineCatalogueRow.degreeEight_order_dvd_twentyOne_of_solubleFlag
    r (hrDegree.trans hdegree) hrSoluble

/-- A soluble point stabilizer in a literal primitive affine action of
degree sixteen has order dividing `360`. -/
theorem degreeSixteen_soluble_card_dvd_threeSixty
    {G Ω : Type} [Group G] [Finite G] [Fintype Ω]
    [MulAction G Ω] [FaithfulSMul G Ω]
    (D : BinaryAffineSmallCatalogueData)
    (hprimitive : MulAction.IsPreprimitive G Ω)
    (P : PrimitiveAffineProfile G Ω)
    (x : Ω) (hdegree : Nat.card Ω = 16)
    (hsolvable : IsSolvable (P.complement x)) :
    Nat.card (P.complement x) ∣ 360 := by
  obtain ⟨r, hrDegree, ⟨e⟩⟩ := D.locate hprimitive P x
    (Or.inr hdegree)
  have hrepSolvable : IsSolvable (D.representative r).Carrier :=
    isSolvable_target_of_mulEquiv e hsolvable
  have hrSoluble : r.nonsoluble = false :=
    representative_is_soluble_row D r hrepSolvable
  rw [Nat.card_congr e.toEquiv, (D.representativeFacts r).card_eq]
  exact SmallAffineCatalogueRow.degreeSixteen_order_dvd_threeSixty_of_solubleFlag
    r (hrDegree.trans hdegree) hrSoluble

/-- Catalogue transport for an arbitrary literal primitive affine action.
This is the form used by an imprimitive ambient action on one of its actual
minimal blocks. -/
theorem chief_abelianLength_le_rowCap
    {G Ω : Type} [Group G] [Finite G] [Fintype Ω]
    [MulAction G Ω] [FaithfulSMul G Ω]
    (D : BinaryAffineSmallCatalogueData)
    (hprimitive : MulAction.IsPreprimitive G Ω)
    (P : PrimitiveAffineProfile G Ω)
    (x : Ω) (s : ActualChiefSeries (P.complement x))
    (hnonsolvable : ¬ IsSolvable (P.complement x))
    (hdegree : Nat.card Ω = 8 ∨ Nat.card Ω = 16) :
    ∃ r : SmallAffineCatalogueRow,
      r.degree = Nat.card Ω ∧
      r.nonsoluble = true ∧
      actualChiefSeriesAbelianLength s ≤ r.nonsolubleAbelianCap := by
  obtain ⟨r, hrDegree, ⟨e⟩⟩ := D.locate hprimitive P x hdegree
  have hrepNonsolvable : ¬ IsSolvable (D.representative r).Carrier :=
    not_isSolvable_target_of_mulEquiv e hnonsolvable
  have hrNonsoluble : r.nonsoluble = true :=
    representative_is_nonsoluble_row D r hrepNonsolvable
  refine ⟨r, hrDegree, hrNonsoluble, ?_⟩
  let K := (D.representativeFacts r).nonsolubleCore hrNonsoluble
  have hseries := K.chief_bound (actualChiefSeriesComap e.symm s)
  rw [actualChiefSeriesComap_abelianLength e.symm s] at hseries
  exact hseries

/-- Fixed-target-envelope wrapper around the literal-chief-series result. -/
theorem trace_abelianLength_le_rowCap
    {G Ω : Type} [Group G] [Finite G] [Fintype Ω]
    [MulAction G Ω] [FaithfulSMul G Ω]
    (D : BinaryAffineSmallCatalogueData)
    (hprimitive : MulAction.IsPreprimitive G Ω)
    (P : PrimitiveAffineProfile G Ω)
    (x : Ω) (T : FixedTargetCompositionTrace (P.complement x))
    (hnonsolvable : ¬ IsSolvable (P.complement x))
    (hdegree : Nat.card Ω = 8 ∨ Nat.card Ω = 16) :
    ∃ r : SmallAffineCatalogueRow,
      r.degree = Nat.card Ω ∧
      r.nonsoluble = true ∧
      T.envelope.abelianLength ≤ r.nonsolubleAbelianCap := by
  obtain ⟨r, hr, hn, hle⟩ := chief_abelianLength_le_rowCap
    D hprimitive P x T.chief hnonsolvable hdegree
  exact ⟨r, hr, hn, T.abelianLength_eq.trans_le hle⟩

/-- A nonsoluble primitive affine complement of degree `8` has no abelian
composition factor. -/
theorem degreeEight_abelianLength_eq_zero
    (D : BinaryAffineSmallCatalogueData)
    (U : PreE7NonPairActionClass 8)
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction 8 U) (Fin 8))
    (P : PrimitiveAffineProfile (preE7NonPairAction 8 U) (Fin 8))
    (x : Fin 8) (T : FixedTargetCompositionTrace (P.complement x))
    (hnonsolvable : ¬ IsSolvable (P.complement x)) :
    T.envelope.abelianLength = 0 := by
  obtain ⟨r, hrDegree, hrNonsoluble, hcap⟩ :=
    trace_abelianLength_le_rowCap D hprimitive P x T hnonsolvable
      (Or.inl (by norm_num))
  have hzero : r.nonsolubleAbelianCap ≤ 0 :=
    SmallAffineCatalogueRow.degreeEight_cap_le r
      (by simpa only [Nat.card_fin] using hrDegree) hrNonsoluble
  omega

/-- A nonsoluble primitive affine complement of degree `16` has at most two
abelian composition factors. -/
theorem degreeSixteen_abelianLength_le_two
    (D : BinaryAffineSmallCatalogueData)
    (U : PreE7NonPairActionClass 16)
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction 16 U) (Fin 16))
    (P : PrimitiveAffineProfile (preE7NonPairAction 16 U) (Fin 16))
    (x : Fin 16) (T : FixedTargetCompositionTrace (P.complement x))
    (hnonsolvable : ¬ IsSolvable (P.complement x)) :
    T.envelope.abelianLength ≤ 2 := by
  obtain ⟨r, hrDegree, hrNonsoluble, hcap⟩ :=
    trace_abelianLength_le_rowCap D hprimitive P x T hnonsolvable
      (Or.inr (by norm_num))
  exact hcap.trans
    (SmallAffineCatalogueRow.degreeSixteen_cap_le r
      (by simpa only [Nat.card_fin] using hrDegree) hrNonsoluble)

end BinaryAffineSmallCatalogueBridge

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
