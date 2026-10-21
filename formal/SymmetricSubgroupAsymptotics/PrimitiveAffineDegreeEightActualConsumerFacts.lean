import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeEightCanonicalComplements
import SymmetricSubgroupAsymptotics.SmallAffineCanonicalFixedFacts
import SymmetricSubgroupAsymptotics.BinaryAffineSmallCatalogueBridge

/-! Degree8 consumer facts use the proved actual degree8 locator directly.
They do not request the old bundled8/16 locator or any published16 input. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineDegreeEightActualConsumerFacts

variable {G X : Type} [Group G] [Finite G] [Fintype X]
    [MulAction G X] [FaithfulSMul G X]
    (hp : MulAction.IsPreprimitive G X) (P : PrimitiveAffineProfile G X)
    (x : X) (hr : Nat.card X=8)

include hp hr

/-- Literal degree8 soluble complement order and row flag, with the actual
complement equivalence supplied by the already proved degree8 theorem. -/
theorem locate_soluble (hs : IsSolvable (P.complement x)) :
    ∃ r : SmallAffineCatalogueRow,r.degree=Nat.card X ∧ r.nonsoluble=false ∧
      Nat.card (P.complement x)=r.complementOrder := by
  letI : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp (by rw [hr]; decide)
  obtain ⟨r,hd,⟨e⟩⟩ :=
    PrimitiveAffineDegreeEightCanonicalComplements.catalogue_locator P hp x hr
  have hrep : IsSolvable (SmallAffineCanonicalRepresentatives.representative r).Carrier := by
    letI : IsSolvable (P.complement x) := hs
    exact solvable_of_surjective (f := e.toMonoidHom) e.surjective
  exact ⟨r,hd,(SmallAffineCanonicalFixedFacts.proved r).solvable_iff.mp hrep,
    (Nat.card_congr e.toEquiv).trans (SmallAffineCanonicalFixedFacts.proved r).card_eq⟩

theorem soluble_card_dvd_twentyOne (hs : IsSolvable (P.complement x)) :
    Nat.card (P.complement x)∣21 := by
  obtain ⟨r,hd,hs,ho⟩ := locate_soluble hp P x hr hs
  rw [ho]
  exact SmallAffineCatalogueRow.degreeEight_order_dvd_twentyOne_of_solubleFlag
    r (hd.trans hr) hs

/-- No abelian chief factor occurs in an actual nonsoluble degree8
complement. Only the fixed facts of its actual located representative enter. -/
theorem nonsoluble_chief_abelianLength_eq_zero
    (T : ActualChiefSeries (P.complement x)) (hn : ¬IsSolvable (P.complement x)) :
    actualChiefSeriesAbelianLength T=0 := by
  letI : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp (by rw [hr]; decide)
  obtain ⟨r,hd,⟨e⟩⟩ :=
    PrimitiveAffineDegreeEightCanonicalComplements.catalogue_locator P hp x hr
  have hrep : ¬IsSolvable (SmallAffineCanonicalRepresentatives.representative r).Carrier := by
    intro hs
    letI := hs
    exact hn (solvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective)
  have hflag : r.nonsoluble=true := by
    cases he : r.nonsoluble with
    | false => exact (hrep ((SmallAffineCanonicalFixedFacts.proved r).solvable_iff.mpr he)).elim
    | true => rfl
  let C := (SmallAffineCanonicalFixedFacts.proved r).nonsolubleCore hflag
  have hc := C.chief_bound (actualChiefSeriesComap e.symm T)
  rw [actualChiefSeriesComap_abelianLength e.symm T] at hc
  have hz := SmallAffineCatalogueRow.degreeEight_cap_le r (hd.trans hr) hflag
  omega

theorem nonsoluble_trace_abelianLength_eq_zero
    (T : FixedTargetCompositionTrace (P.complement x)) (hn : ¬IsSolvable (P.complement x)) :
    T.envelope.abelianLength=0 :=
  T.abelianLength_eq.trans (nonsoluble_chief_abelianLength_eq_zero hp P x hr T.chief hn)

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineDegreeEightActualConsumerFacts
