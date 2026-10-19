import SymmetricSubgroupAsymptotics.PrimitiveSixFinalPublishedNormalGenerators
import SymmetricSubgroupAsymptotics.ThreePairNormalGenerators
import SymmetricSubgroupAsymptotics.SixPointTernaryAxesNormalGenerators
import SymmetricSubgroupAsymptotics.SixPointTernaryQuarterTurnNormalGenerators
import SymmetricSubgroupAsymptotics.BinaryConjugacyTransport

/-! Capacity-free structural charts for an actual transitive six-point
group. The charts contain physical pair frames or literal point-conjugate
model inclusions, never a normal-generator/capacity premise. Recognition
of an arbitrary two-triple frame into these charts is a separate leaf. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise Classical
namespace SymmetricSubgroupAsymptotics.TransitiveSixNormalGeneratorCharts
open Non2UnipotentPrefixFiniteMenu

inductive Chart (P : Subgroup (Equiv.Perm (Fin 6))) : Type
  | primitive (hp : MulAction.IsPreprimitive P (Fin 6))
  | threePairs (frame : BinaryPairFrame P (Fin 3))
  | axes (c : Equiv.Perm (Fin 6))
      (hle : MulAut.conj c • P ≤ SixPointTernaryAxesNormalGenerators.literalAction.range)
  | quarter (c : Equiv.Perm (Fin 6))
      (hle : MulAut.conj c • P ≤ SixPointTernaryQuarterTurnNormalGenerators.literalAction.range)
      (lift : SixPointTernaryQuarterTurnNormalGenerators.Model)
      (hmem : SixPointTernaryQuarterTurnNormalGenerators.literalAction lift ∈ MulAut.conj c • P)
      (hupper : lift.right = SixPointTernaryQuarterTurnNormalGenerators.gen)
  | fullWreath (c : Equiv.Perm (Fin 6))
      (heq : MulAut.conj c • P = SixPairLocalWreathSocles.literalAction.range)

theorem normal_generating_pairs
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence)
    (P : Subgroup (Equiv.Perm (Fin 6))) [MulAction.IsPretransitive P (Fin 6)]
    (C : Chart P) : ∀ N : Subgroup P, N.Normal →
      ∃ x : Fin 2 → P, Subgroup.normalClosure (Set.range x) = N := by
  cases C with
  | primitive hp =>
      letI := hp
      intro N hN
      letI := hN
      apply exists_normal_generating_tuple_of_normalGen_le N
      exact (PrimitiveSixFinalPublishedNormalGenerators.normalGen_le_one socle catalogue P N).trans (by decide)
  | threePairs frame =>
      intro N hN
      letI := hN
      exact exists_normal_generating_tuple_of_normalGen_le N
        (ThreePairNormalGenerators.normalGen_le_of_transitive frame N)
  | axes c hle =>
      let e : P ≃* (MulAut.conj c • P : Subgroup (Equiv.Perm (Fin 6))) := actionConjugacyEquiv c rfl
      exact normal_generating_tuples_of_surjective e.symm.toMonoidHom e.symm.surjective
        (SixPointTernaryAxesNormalGenerators.normal_generating_pairs _ hle)
  | quarter c hle lift hmem hupper =>
      let e : P ≃* (MulAut.conj c • P : Subgroup (Equiv.Perm (Fin 6))) := actionConjugacyEquiv c rfl
      exact normal_generating_tuples_of_surjective e.symm.toMonoidHom e.symm.surjective
        (SixPointTernaryQuarterTurnNormalGenerators.normal_generating_pairs _ hle lift hmem hupper)
  | fullWreath c heq =>
      let e : P ≃* SixPairLocalWreathSocles.literalAction.range := actionConjugacyEquiv c heq
      apply normal_generating_tuples_of_surjective e.symm.toMonoidHom e.symm.surjective
      intro N hN
      letI := hN
      exact exists_normal_generating_tuple_of_normalGen_le N
        (SixPairLocalWreathSocles.image_normalGen N hN)

theorem quotientSocle_of_original_natural
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence)
    {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 6))
    [MulAction.IsPretransitive F.top.range (Fin 6)]
    (C : Chart F.top.range)
    (hnatural : UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) U X) 1)
    (N : Subgroup U) [N.Normal] : SocleNormalGeneratorBound (U ⧸ N) 3 := by
  apply F.quotientSocle_of_uniform_pair_action 1 2
    (F.uniform_pair_action_of_original 1 hnatural) ?_ N
  intro L hL
  letI := hL
  obtain ⟨x,hx⟩ := normal_generating_pairs socle catalogue F.top.range C L hL
  exact normalGen_le_of_fin_tuple x hx

end SymmetricSubgroupAsymptotics.TransitiveSixNormalGeneratorCharts
