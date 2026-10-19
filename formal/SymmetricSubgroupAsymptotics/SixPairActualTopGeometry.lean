import SymmetricSubgroupAsymptotics.SixPairPrimitiveRepresentativeSource
import SymmetricSubgroupAsymptotics.OriginalMinimalBlockProductFrame

/-! Actual six-point top geometry partitions the whole representative
family: the primitive branch has a constructed complete source, and every
remaining action carries an actual three-pair or two-triple product frame.
No stored action number or finite normal metadata enters this partition. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.SixPairActualTopGeometry
open Non2UnipotentPrefixFiniteMenu

inductive ImprimitiveGeometry (P : Subgroup (Equiv.Perm (Fin 6))) : Type 1 where
  | threePairs (frame : ProductBlockFrame P (Fin 3) (ZMod 2))
  | twoTriples (frame : ProductBlockFrame P (Fin 2) (ZMod 3))

/-- Minimal blocks are chosen in the ACTUAL faithful top range. -/
def imprimitiveGeometry (P : Subgroup (Equiv.Perm (Fin 6)))
    [MulAction.IsPretransitive P (Fin 6)]
    (hp : ¬MulAction.IsPreprimitive P (Fin 6)) : ImprimitiveGeometry P := by
  apply Classical.choice
  obtain ⟨D⟩ := originalMinimalBlock_nonempty (A := P) (0 : Fin 6) hp
  obtain ⟨hf,hi⟩ := D.degrees_ge_two
  have hprod : Nat.card D.Fibre*Nat.card D.Points=6 := by
    simpa only [Nat.card_fin] using D.degree_product
  have hcases : (Nat.card D.Fibre=2 ∧ Nat.card D.Points=3) ∨
      (Nat.card D.Fibre=3 ∧ Nat.card D.Points=2) := by
    have hsmall : Nat.card D.Fibre=2 ∨ Nat.card D.Points=2 := by
      by_contra h
      push_neg at h
      have ha : 3≤Nat.card D.Fibre := by omega
      have hb : 3≤Nat.card D.Points := by omega
      nlinarith
    rcases hsmall with h | h
    · left
      refine ⟨h,?_⟩
      rw [h] at hprod
      omega
    · right
      refine ⟨?_,h⟩
      rw [h] at hprod
      omega
  rcases hcases with ⟨hf,hi⟩ | ⟨hf,hi⟩
  · exact ⟨.threePairs (D.productFrame (Finite.equivFinOfCardEq hi)
      ((Finite.equivFinOfCardEq hf).trans (ZMod.finEquiv 2).toEquiv))⟩
  · exact ⟨.twoTriples (D.productFrame (Finite.equivFinOfCardEq hi)
      ((Finite.equivFinOfCardEq hf).trans (ZMod.finEquiv 3).toEquiv))⟩

/-- The entire actual representative space is covered by this constructive
alternative. The two remaining branches retain their original top action. -/
def source_or_imprimitive
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence)
    (h6 : PublishedPrimitiveDegreeSixClassification) (hZmud : ZmudFaithfulCharacterTupleInput)
    (p : PreE7PairActionClass 6)
    (F : BinaryPairFrame (preE7PairAction 6 p) (Fin 6))
    [MulAction.IsPretransitive (preE7PairAction 6 p) (Fin 12)] :
    PreE7RankTailSourceOrYonedaTopData 12 (preE7SixPairNonPairAction p) ⊕
      ImprimitiveGeometry F.top.range := by
  letI : MulAction.IsPretransitive F.top.range (Fin 6) := F.top_pretransitive
  by_cases hp : MulAction.IsPreprimitive F.top.range (Fin 6)
  · letI := hp
    exact .inl (SixPairPrimitiveRepresentativeSource.source socle catalogue h6 hZmud p F)
  · exact .inr (imprimitiveGeometry F.top.range hp)

end SymmetricSubgroupAsymptotics.SixPairActualTopGeometry
