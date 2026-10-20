import SymmetricSubgroupAsymptotics.ProductBlockFrameKernelCoordinates
import SymmetricSubgroupAsymptotics.PrimitiveSixFinalPublishedNormalGenerators
import SymmetricSubgroupAsymptotics.SubdirectPairNormalGenerators
import SymmetricSubgroupAsymptotics.NormalGeneratingTuplesExtension

/-! Three slots for an actual two-block action with primitive six-point
kernel components. This retains every diagonal/full-product correlation.
Together with natural capacity one, (3,1) is an existing admissible profile. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ProductBlockFrame
open Non2UnipotentPrefixFiniteMenu

theorem normal_triples_of_two_primitive_six_components
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence)
    {X : Type} {U : Subgroup (Equiv.Perm X)}
    (C : ProductBlockFrame U (Fin 2) (Fin 6)) (htop : Function.Surjective C.top)
    [MulAction.IsPreprimitive (C.kernelCoordinate 0).range (Fin 6)]
    [MulAction.IsPreprimitive (C.kernelCoordinate 1).range (Fin 6)] :
    ∀ N : Subgroup U, N.Normal →
      ∃ x : Fin 3 → U, Subgroup.normalClosure (Set.range x) = N := by
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  letI : IsCyclic (Equiv.Perm (Fin 2)) := isCyclic_of_prime_card (p := 2) (by
    norm_num [Nat.card_eq_fintype_card,Fintype.card_perm])
  have hK : ∀ N : Subgroup C.top.ker, N.Normal →
      ∃ x : Fin 2 → C.top.ker, Subgroup.normalClosure (Set.range x) = N := by
    apply normal_generating_tuples_subdirect_pair (a := 1) (b := 1)
      (C.kernelCoordinate 0).rangeRestrict (C.kernelCoordinate 1).rangeRestrict
      (C.kernelCoordinate 0).rangeRestrict_surjective (C.kernelCoordinate 1).rangeRestrict_surjective
    · intro x y h
      apply C.twoKernelMap_injective
      exact Prod.ext (congrArg Subtype.val (congrArg Prod.fst h))
        (congrArg Subtype.val (congrArg Prod.snd h))
    · exact PrimitiveSixFinalPublishedNormalGenerators.normal_generating_singletons socle catalogue _
    · exact PrimitiveSixFinalPublishedNormalGenerators.normal_generating_singletons socle catalogue _
  exact normal_generating_tuples_cyclic_extension C.top htop hK

theorem quotientSocle_three_of_two_primitive_six_components
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence)
    {X : Type} {U : Subgroup (Equiv.Perm X)}
    (C : ProductBlockFrame U (Fin 2) (Fin 6)) (htop : Function.Surjective C.top)
    [MulAction.IsPreprimitive (C.kernelCoordinate 0).range (Fin 6)]
    [MulAction.IsPreprimitive (C.kernelCoordinate 1).range (Fin 6)]
    (N : Subgroup U) [N.Normal] : SocleNormalGeneratorBound (U ⧸ N) 3 :=
  quotientSocleNormalGeneratorBound_of_normal_generating_tuples
    (normal_triples_of_two_primitive_six_components socle catalogue C htop) N

end SymmetricSubgroupAsymptotics.ProductBlockFrame
