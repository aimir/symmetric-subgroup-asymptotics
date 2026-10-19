import SymmetricSubgroupAsymptotics.PrimitiveTwelveExactProfileNormalGenerators
import SymmetricSubgroupAsymptotics.PrimitiveCatalogueClassificationPublished
import SymmetricSubgroupAsymptotics.PrimitiveAffineProfileParity
import SymmetricSubgroupAsymptotics.BinaryConjugacyTransport
import Mathlib.GroupTheory.Perm.Cycle.Type

/-! Normal generation and every quotient socle in an actual primitive
twelve-point action follow from the two published inputs already present at
final T1: the primitive socle dichotomy and bounded primitive catalogue.
The passage through the PreE7 index is an actual point conjugacy. There is
no new degree-twelve classification, finite row data, or desired rank input. -/

set_option autoImplicit false
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics.PrimitiveTwelveFinalPublishedNormalGenerators

open Non2UnipotentPrefixFiniteMenu
open PrimitiveTwelveExactProfileNormalGenerators

theorem not_isPGroup (P : Subgroup (Equiv.Perm (Fin 12)))
    [MulAction.IsPretransitive P (Fin 12)] : ¬ IsPGroup 2 P := by
  intro htwo
  obtain ⟨d,hd⟩ := htwo.card_orbit (0 : Fin 12)
  have hc : Nat.card (MulAction.orbit P (0 : Fin 12)) = 12 := by
    rw [MulAction.orbit_eq_univ]
    exact (Nat.card_congr (Equiv.Set.univ (Fin 12))).trans (Nat.card_fin 12)
  rw [hc] at hd
  exact twelve_not_two_power d hd

/-- An actual primitive twelve-point subgroup has an exact nonaffine profile
on a point-conjugate PreE7 representative, using the existing socle input. -/
theorem exists_exact_profile
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (P : Subgroup (Equiv.Perm (Fin 12))) [MulAction.IsPreprimitive P (Fin 12)] :
    ∃ (U : PreE7NonPairActionClass 12) (c : Equiv.Perm (Fin 12)),
      MulAut.conj c • P = preE7NonPairAction 12 U ∧
      MulAction.IsPreprimitive (preE7NonPairAction 12 U) (Fin 12) ∧
      Nonempty (ExactPrimitiveSemisimpleOuterLogProfile (preE7NonPairAction 12 U) 12) := by
  obtain ⟨i,c,hc⟩ := Non2TransitiveActionClass.representative_cover P
    (not_isPGroup P) inferInstance
  have hpre : IsPreE7ActionClass 12 i := by
    intro d hd
    have hge := d.pairCount_ge_24
    change 2 * d.pairCount = 12 at hd
    omega
  let J : PreE7ActionClass 12 := ⟨i,hpre⟩
  have hnopair : IsPreE7NonPairActionClass 12 J := by
    intro d hd
    have hge := d.pairCount_ge_24
    omega
  let U : PreE7NonPairActionClass 12 := ⟨J,hnopair⟩
  let e : P ≃* i.representative := actionConjugacyEquiv c hc
  let f : MulActionHom e (Fin 12) (Fin 12) := {
    toFun := c
    map_smul' := by
      intro g x
      change c (g.1 x) = c (g.1 (c.symm (c x)))
      rw [c.symm_apply_apply] }
  have hp : MulAction.IsPreprimitive (preE7NonPairAction 12 U) (Fin 12) :=
    MulAction.IsPreprimitive.of_surjective (f := f) c.surjective
  rcases socle.primitive 12 U (by decide) hp with D | affine
  · exact ⟨U,c,hc,hp,⟨D⟩⟩
  · have ht : affine.p = 2 := affine.prime_eq_two_of_even_degree (0 : Fin 12) (by decide)
    obtain ⟨d,hd⟩ := affine.degree_eq_prime_power (0 : Fin 12)
    rw [ht] at hd
    exact False.elim (twelve_not_two_power d hd)

/-- This theorem's only literature parameters are precisely the two
published inputs already in the final T1 signature. -/
theorem normal_generating_singletons
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence)
    (P : Subgroup (Equiv.Perm (Fin 12))) [MulAction.IsPreprimitive P (Fin 12)] :
    ∀ N : Subgroup P, N.Normal →
      ∃ x : Fin 1 → P, Subgroup.normalClosure (Set.range x) = N := by
  obtain ⟨U,c,hc,hp,⟨D⟩⟩ := exists_exact_profile socle P
  letI := hp
  let e : P ≃* preE7NonPairAction 12 U := actionConjugacyEquiv c hc
  exact normal_generating_tuples_of_surjective e.symm.toMonoidHom e.symm.surjective
    (PrimitiveTwelveExactProfileNormalGenerators.normal_generating_singletons D catalogue)

theorem normalGen_le_one
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence)
    (P : Subgroup (Equiv.Perm (Fin 12))) [MulAction.IsPreprimitive P (Fin 12)]
    (N : Subgroup P) [N.Normal] : MarkedC4.normalGen N ≤ 1 := by
  obtain ⟨x,hx⟩ := normal_generating_singletons socle catalogue P N inferInstance
  exact normalGen_le_of_fin_tuple x hx

/-- The chain is on the original literal group, not only its representative. -/
theorem normal_total
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence)
    (P : Subgroup (Equiv.Perm (Fin 12))) [MulAction.IsPreprimitive P (Fin 12)]
    (A B : Subgroup P) (hA : A.Normal) (hB : B.Normal) : A≤B ∨ B≤A := by
  obtain ⟨U,c,hc,hp,⟨D⟩⟩ := exists_exact_profile socle P
  letI := hp
  let e : P ≃* preE7NonPairAction 12 U := actionConjugacyEquiv c hc
  exact normalSubgroups_total_of_surjective e.symm.toMonoidHom e.symm.surjective
    (PrimitiveTwelveExactProfileNormalGenerators.normal_total D catalogue) A B hA hB

/-- Every same-original denominator inherits the one-generator socle bound. -/
theorem quotientSocle_one
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence)
    (P : Subgroup (Equiv.Perm (Fin 12))) [MulAction.IsPreprimitive P (Fin 12)]
    (N : Subgroup P) [N.Normal] : SocleNormalGeneratorBound (P ⧸ N) 1 :=
  quotientSocleNormalGeneratorBound_one_of_normal_total (normal_total socle catalogue P) N

end SymmetricSubgroupAsymptotics.PrimitiveTwelveFinalPublishedNormalGenerators
end
