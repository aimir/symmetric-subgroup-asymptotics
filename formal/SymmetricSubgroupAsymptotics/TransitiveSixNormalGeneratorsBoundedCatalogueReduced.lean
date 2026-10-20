import SymmetricSubgroupAsymptotics.TransitiveSixNormalGenerators
import SymmetricSubgroupAsymptotics.PrimitiveSixTwelveNormalConsumerFacts
import Mathlib.Tactic.FinCases
import SymmetricSubgroupAsymptotics.TransitiveSixNormalGeneratorChartsBoundedCatalogueReduced

/-! Isolated actual degree6/12 normal-consumer route. Original records,
finite index sets and all certificate declarations are imported unchanged. -/
set_option autoImplicit false

noncomputable section

open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics.TransitiveSixNormalGenerators

namespace BoundedCatalogueReduced

open Non2UnipotentPrefixFiniteMenu

private theorem of_two_triples
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PrimitiveSixTwelveNormalConsumerFacts)
    (P : Subgroup (Equiv.Perm (Fin 6))) [MulAction.IsPretransitive P (Fin 6)]
    (F : ProductBlockFrame P (Fin 2) (ZMod 3)) :
    ∀ N : Subgroup P, N.Normal →
      ∃ x : Fin 2 → P, Subgroup.normalClosure (Set.range x) = N := by
  let c := TwoTripleProductFrameRecognition.conjugator F
  let Q : Subgroup (Equiv.Perm (Fin 6)) := MulAut.conj c • P
  let e : P ≃* Q := actionConjugacyEquiv c rfl
  letI : MulAction.IsPretransitive Q (Fin 6) := ⟨fun x y => by
    obtain ⟨p,hp⟩ := MulAction.exists_smul_eq P (c.symm x) (c.symm y)
    refine ⟨e p,?_⟩
    change c ((p : Equiv.Perm (Fin 6)) (c.symm x)) = y
    rw [show (p : Equiv.Perm (Fin 6)) (c.symm x) = c.symm y from hp]
    exact c.apply_symm_apply y⟩
  have hle : Q ≤ SixPairLocalWreathSocles.literalAction.range :=
    TwoTripleProductFrameRecognition.conjugate_le F
  exact normal_generating_tuples_of_surjective e.symm.toMonoidHom e.symm.surjective
    (_root_.SymmetricSubgroupAsymptotics.TransitiveSixNormalGeneratorCharts.BoundedCatalogueReduced.normal_generating_pairs socle catalogue Q
      (TransitiveTwoTripleSubgroupRecognition.chart Q hle))

theorem normal_generating_pairs
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PrimitiveSixTwelveNormalConsumerFacts)
    (P : Subgroup (Equiv.Perm (Fin 6))) [MulAction.IsPretransitive P (Fin 6)] :
    ∀ N : Subgroup P, N.Normal →
      ∃ x : Fin 2 → P, Subgroup.normalClosure (Set.range x) = N := by
  by_cases hp : MulAction.IsPreprimitive P (Fin 6)
  · exact _root_.SymmetricSubgroupAsymptotics.TransitiveSixNormalGeneratorCharts.BoundedCatalogueReduced.normal_generating_pairs socle catalogue P
      (.primitive hp)
  obtain ⟨D⟩ := originalMinimalBlock_nonempty (A := P) (0 : Fin 6) hp
  obtain ⟨hf,hi⟩ := D.degrees_ge_two
  have hprod : Nat.card D.Fibre * Nat.card D.Points = 6 := by
    simpa only [Nat.card_fin] using D.degree_product
  have hcases : (Nat.card D.Fibre = 2 ∧ Nat.card D.Points = 3) ∨
      (Nat.card D.Fibre = 3 ∧ Nat.card D.Points = 2) := by
    have hsmall : Nat.card D.Fibre = 2 ∨ Nat.card D.Points = 2 := by
      by_contra h
      push_neg at h
      have ha : 3 ≤ Nat.card D.Fibre := by omega
      have hb : 3 ≤ Nat.card D.Points := by omega
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
  · let eI : D.Points ≃ Fin 3 := Finite.equivFinOfCardEq hi
    let eF : D.Fibre ≃ ZMod 2 :=
      (Finite.equivFinOfCardEq hf).trans (ZMod.finEquiv 2).toEquiv
    let F := D.productFrame eI eF
    exact _root_.SymmetricSubgroupAsymptotics.TransitiveSixNormalGeneratorCharts.BoundedCatalogueReduced.normal_generating_pairs socle catalogue P
      (.threePairs ⟨F.frame,F.top,F.intertwine⟩)
  · let eI : D.Points ≃ Fin 2 := Finite.equivFinOfCardEq hi
    let eF : D.Fibre ≃ ZMod 3 :=
      (Finite.equivFinOfCardEq hf).trans (ZMod.finEquiv 3).toEquiv
    exact _root_.SymmetricSubgroupAsymptotics.TransitiveSixNormalGenerators.BoundedCatalogueReduced.of_two_triples socle catalogue P (D.productFrame eI eF)

theorem normalGen_le_two
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PrimitiveSixTwelveNormalConsumerFacts)
    (P : Subgroup (Equiv.Perm (Fin 6))) [MulAction.IsPretransitive P (Fin 6)]
    (N : Subgroup P) [N.Normal] : MarkedC4.normalGen N ≤ 2 := by
  obtain ⟨x,hx⟩ := _root_.SymmetricSubgroupAsymptotics.TransitiveSixNormalGenerators.BoundedCatalogueReduced.normal_generating_pairs socle catalogue P N inferInstance
  exact normalGen_le_of_fin_tuple x hx

end BoundedCatalogueReduced

end SymmetricSubgroupAsymptotics.TransitiveSixNormalGenerators

