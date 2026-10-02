import SymmetricSubgroupAsymptotics.PrimitiveAffineSmallPublishedCatalogue
import SymmetricSubgroupAsymptotics.UniqueMinimalNormalAbelianLength

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

namespace PrimitiveAffineSmallCatalogueBridge

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
    (L : PublishedSmallAffineCatalogueLocator)
    (C : SmallAffineCatalogueReceipt L)
    (r : SmallAffineCatalogueRow)
    (h : IsSolvable (L.representative r).Carrier) :
    r.nonsoluble = false :=
  (C r).solvable_iff.mp h

private theorem representative_is_nonsoluble_row
    (L : PublishedSmallAffineCatalogueLocator)
    (C : SmallAffineCatalogueReceipt L)
    (r : SmallAffineCatalogueRow)
    (h : ¬ IsSolvable (L.representative r).Carrier) :
    r.nonsoluble = true := by
  cases hr : r.nonsoluble with
  | false => exact (h ((C r).solvable_iff.mpr hr)).elim
  | true => rfl

/-- The soluble degree-`27` order bound, with primitivity made explicit.

The proof uses only the published catalogue locator, the exact
representative order/solubility facts, and the finite row calculation that
the largest soluble degree-`27` complement has order `78`. -/
theorem degreeTwentySeven_card_le
    (L : PublishedSmallAffineCatalogueLocator)
    (C : SmallAffineCatalogueReceipt L)
    (U : PreE7NonPairActionClass 27)
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction 27 U) (Fin 27))
    (P : PrimitiveAffineProfile (preE7NonPairAction 27 U) (Fin 27))
    (x : Fin 27) (hsolvable : IsSolvable (P.complement x)) :
    Nat.card (P.complement x) ≤ 78 := by
  obtain ⟨r, hrDegree, ⟨e⟩⟩ := L.locate U hprimitive P x
    (Or.inr (Or.inr rfl))
  have hrepSolvable : IsSolvable (L.representative r).Carrier :=
    isSolvable_target_of_mulEquiv e hsolvable
  have hrSoluble : r.nonsoluble = false :=
    representative_is_soluble_row L C r hrepSolvable
  rw [Nat.card_congr e.toEquiv, (C r).card_eq]
  exact SmallAffineCatalogueRow.degreeTwentySeven_order_le_of_solubleFlag
    r hrDegree hrSoluble

private theorem trace_abelianLength_le_rowCap
    {w : ℕ}
    (L : PublishedSmallAffineCatalogueLocator)
    (C : SmallAffineCatalogueReceipt L)
    (U : PreE7NonPairActionClass w)
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction w U) (Fin w))
    (P : PrimitiveAffineProfile (preE7NonPairAction w U) (Fin w))
    (x : Fin w) (T : FixedTargetCompositionTrace (P.complement x))
    (hnonsolvable : ¬ IsSolvable (P.complement x))
    (hdegree : w = 8 ∨ w = 16 ∨ w = 27) :
    ∃ r : SmallAffineCatalogueRow,
      r.degree = w ∧
      r.nonsoluble = true ∧
      T.envelope.abelianLength ≤ r.nonsolubleAbelianCap := by
  obtain ⟨r, hrDegree, ⟨e⟩⟩ := L.locate U hprimitive P x hdegree
  have hrepNonsolvable : ¬ IsSolvable (L.representative r).Carrier :=
    not_isSolvable_target_of_mulEquiv e hnonsolvable
  have hrNonsoluble : r.nonsoluble = true :=
    representative_is_nonsoluble_row L C r hrepNonsolvable
  refine ⟨r, hrDegree, hrNonsoluble, ?_⟩
  let K := (C r).nonsolubleCore hrNonsoluble
  letI : K.core.Normal := K.normal
  rw [T.abelianLength_eq]
  have hseries := actualChiefSeriesAbelianLength_le_quotient_cardFactors
    (actualChiefSeriesComap e.symm T.chief) K.core K.ne_bot
      K.noncommutative K.le_every_nontrivial_normal
  rw [actualChiefSeriesComap_abelianLength e.symm T.chief,
    K.quotient_card_eq] at hseries
  exact hseries.trans
    (SmallAffineCatalogueRow.nonsolubleCoreQuotient_cardFactors_le
      r hrNonsoluble)

/-- A nonsoluble primitive affine complement of degree `8` has no abelian
composition factor. -/
theorem degreeEight_abelianLength_eq_zero
    (L : PublishedSmallAffineCatalogueLocator)
    (C : SmallAffineCatalogueReceipt L)
    (U : PreE7NonPairActionClass 8)
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction 8 U) (Fin 8))
    (P : PrimitiveAffineProfile (preE7NonPairAction 8 U) (Fin 8))
    (x : Fin 8) (T : FixedTargetCompositionTrace (P.complement x))
    (hnonsolvable : ¬ IsSolvable (P.complement x)) :
    T.envelope.abelianLength = 0 := by
  obtain ⟨r, hrDegree, hrNonsoluble, hcap⟩ :=
    trace_abelianLength_le_rowCap L C U hprimitive P x T hnonsolvable
      (Or.inl rfl)
  have hzero : r.nonsolubleAbelianCap ≤ 0 :=
    SmallAffineCatalogueRow.degreeEight_cap_le r hrDegree hrNonsoluble
  omega

/-- A nonsoluble primitive affine complement of degree `16` has at most two
abelian composition factors. -/
theorem degreeSixteen_abelianLength_le_two
    (L : PublishedSmallAffineCatalogueLocator)
    (C : SmallAffineCatalogueReceipt L)
    (U : PreE7NonPairActionClass 16)
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction 16 U) (Fin 16))
    (P : PrimitiveAffineProfile (preE7NonPairAction 16 U) (Fin 16))
    (x : Fin 16) (T : FixedTargetCompositionTrace (P.complement x))
    (hnonsolvable : ¬ IsSolvable (P.complement x)) :
    T.envelope.abelianLength ≤ 2 := by
  obtain ⟨r, hrDegree, hrNonsoluble, hcap⟩ :=
    trace_abelianLength_le_rowCap L C U hprimitive P x T hnonsolvable
      (Or.inr (Or.inl rfl))
  exact hcap.trans
    (SmallAffineCatalogueRow.degreeSixteen_cap_le r hrDegree hrNonsoluble)

/-- A nonsoluble primitive affine complement of degree `27` has at most one
abelian composition factor. -/
theorem degreeTwentySeven_abelianLength_le_one
    (L : PublishedSmallAffineCatalogueLocator)
    (C : SmallAffineCatalogueReceipt L)
    (U : PreE7NonPairActionClass 27)
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction 27 U) (Fin 27))
    (P : PrimitiveAffineProfile (preE7NonPairAction 27 U) (Fin 27))
    (x : Fin 27) (T : FixedTargetCompositionTrace (P.complement x))
    (hnonsolvable : ¬ IsSolvable (P.complement x)) :
    T.envelope.abelianLength ≤ 1 := by
  obtain ⟨r, hrDegree, hrNonsoluble, hcap⟩ :=
    trace_abelianLength_le_rowCap L C U hprimitive P x T hnonsolvable
      (Or.inr (Or.inr rfl))
  exact hcap.trans
    (SmallAffineCatalogueRow.degreeTwentySeven_cap_le r hrDegree hrNonsoluble)

end PrimitiveAffineSmallCatalogueBridge

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
