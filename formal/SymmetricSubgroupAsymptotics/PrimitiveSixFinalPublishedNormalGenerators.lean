import SymmetricSubgroupAsymptotics.PrimitiveSixExactProfileNormalGenerators
import SymmetricSubgroupAsymptotics.PrimitiveCatalogueClassificationPublished
import SymmetricSubgroupAsymptotics.PrimitiveAffineProfileParity
import SymmetricSubgroupAsymptotics.BinaryConjugacyTransport
import Mathlib.GroupTheory.Perm.Cycle.Type

/-! Normal generation and an order-five element in an actual primitive
six-point action follow from the two published inputs already present at
final T1: the primitive socle dichotomy and bounded primitive catalogue.
The passage through the PreE7 index is an actual point conjugacy. There is
no new degree-six classification, finite row data, or desired rank input. -/

set_option autoImplicit false
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics.PrimitiveSixFinalPublishedNormalGenerators

open Non2UnipotentPrefixFiniteMenu
open PrimitiveSixExactProfileNormalGenerators

theorem not_isPGroup (P : Subgroup (Equiv.Perm (Fin 6)))
    [MulAction.IsPretransitive P (Fin 6)] : ¬ IsPGroup 2 P := by
  intro htwo
  obtain ⟨d,hd⟩ := htwo.card_orbit (0 : Fin 6)
  have hc : Nat.card (MulAction.orbit P (0 : Fin 6)) = 6 := by
    rw [MulAction.orbit_eq_univ]
    exact (Nat.card_congr (Equiv.Set.univ (Fin 6))).trans (Nat.card_fin 6)
  rw [hc] at hd
  exact six_not_two_power d hd

/-- An actual primitive six-point subgroup has an exact nonaffine profile
on a point-conjugate PreE7 representative, using the existing socle input. -/
theorem exists_exact_profile
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (P : Subgroup (Equiv.Perm (Fin 6))) [MulAction.IsPreprimitive P (Fin 6)] :
    ∃ (U : PreE7NonPairActionClass 6) (c : Equiv.Perm (Fin 6)),
      MulAut.conj c • P = preE7NonPairAction 6 U ∧
      MulAction.IsPreprimitive (preE7NonPairAction 6 U) (Fin 6) ∧
      Nonempty (ExactPrimitiveSemisimpleOuterLogProfile (preE7NonPairAction 6 U) 6) := by
  obtain ⟨i,c,hc⟩ := Non2TransitiveActionClass.representative_cover P
    (not_isPGroup P) inferInstance
  have hpre : IsPreE7ActionClass 6 i := by
    intro d hd
    have hge := d.pairCount_ge_24
    change 2 * d.pairCount = 6 at hd
    omega
  let J : PreE7ActionClass 6 := ⟨i,hpre⟩
  have hnopair : IsPreE7NonPairActionClass 6 J := by
    intro d hd
    have hge := d.pairCount_ge_24
    omega
  let U : PreE7NonPairActionClass 6 := ⟨J,hnopair⟩
  let e : P ≃* i.representative := actionConjugacyEquiv c hc
  let f : MulActionHom e (Fin 6) (Fin 6) := {
    toFun := c
    map_smul' := by
      intro g x
      change c (g.1 x) = c (g.1 (c.symm (c x)))
      rw [c.symm_apply_apply] }
  have hp : MulAction.IsPreprimitive (preE7NonPairAction 6 U) (Fin 6) :=
    MulAction.IsPreprimitive.of_surjective (f := f) c.surjective
  rcases socle.primitive 6 U (by decide) hp with D | affine
  · exact ⟨U,c,hc,hp,⟨D⟩⟩
  · have ht : affine.p = 2 := affine.prime_eq_two_of_even_degree (0 : Fin 6) (by decide)
    obtain ⟨d,hd⟩ := affine.degree_eq_prime_power (0 : Fin 6)
    rw [ht] at hd
    exact False.elim (six_not_two_power d hd)

/-- This theorem's only literature parameters are precisely the two
published inputs already in the final T1 signature. -/
theorem normal_generating_singletons
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence)
    (P : Subgroup (Equiv.Perm (Fin 6))) [MulAction.IsPreprimitive P (Fin 6)] :
    ∀ N : Subgroup P, N.Normal →
      ∃ x : Fin 1 → P, Subgroup.normalClosure (Set.range x) = N := by
  obtain ⟨U,c,hc,hp,⟨D⟩⟩ := exists_exact_profile socle P
  letI := hp
  let e : P ≃* preE7NonPairAction 6 U := actionConjugacyEquiv c hc
  exact normal_generating_tuples_of_surjective e.symm.toMonoidHom e.symm.surjective
    (PrimitiveSixExactProfileNormalGenerators.normal_generating_singletons D catalogue)

theorem normalGen_le_one
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence)
    (P : Subgroup (Equiv.Perm (Fin 6))) [MulAction.IsPreprimitive P (Fin 6)]
    (N : Subgroup P) [N.Normal] : MarkedC4.normalGen N ≤ 1 := by
  obtain ⟨x,hx⟩ := normal_generating_singletons socle catalogue P N inferInstance
  exact normalGen_le_of_fin_tuple x hx

theorem five_dvd_card
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence)
    (P : Subgroup (Equiv.Perm (Fin 6))) [MulAction.IsPreprimitive P (Fin 6)] :
    5 ∣ Nat.card P := by
  obtain ⟨U,c,hc,hp,⟨D⟩⟩ := exists_exact_profile socle P
  letI := hp
  let e : P ≃* preE7NonPairAction 6 U := actionConjugacyEquiv c hc
  rw [Nat.card_congr e.toEquiv]
  exact PrimitiveSixExactProfileNormalGenerators.five_dvd_card D catalogue

theorem exists_order_five
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence)
    (P : Subgroup (Equiv.Perm (Fin 6))) [MulAction.IsPreprimitive P (Fin 6)] :
    ∃ g : P, orderOf g = 5 := by
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  exact exists_prime_orderOf_dvd_card' 5 (five_dvd_card socle catalogue P)

end SymmetricSubgroupAsymptotics.PrimitiveSixFinalPublishedNormalGenerators

end
