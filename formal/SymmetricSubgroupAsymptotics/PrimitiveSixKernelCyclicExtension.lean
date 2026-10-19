import SymmetricSubgroupAsymptotics.PrimitiveSixFinalPublishedNormalGenerators
import SymmetricSubgroupAsymptotics.NormalGeneratingTuplesExtension

/-! A faithfully represented actual primitive-six kernel has the published
singleton normal-generation bound. An actual finite cyclic top then gives
two generators for each original normal subgroup, retaining every N. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSixKernelCyclicExtension
open Non2UnipotentPrefixFiniteMenu

theorem normal_pairs
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence)
    {G Q : Type} [Group G] [Group Q] [Finite Q] [IsCyclic Q]
    (pi : G →* Q) (hpi : Function.Surjective pi)
    (f : pi.ker →* Equiv.Perm (Fin 6)) (hf : Function.Injective f)
    [MulAction.IsPreprimitive f.range (Fin 6)] :
    ∀ N : Subgroup G, N.Normal →
      ∃ x : Fin 2 → G, Subgroup.normalClosure (Set.range x) = N := by
  let e : pi.ker ≃* f.range := MulEquiv.ofBijective f.rangeRestrict
    ⟨fun _ _ h => hf (congrArg Subtype.val h), f.rangeRestrict_surjective⟩
  have hK : ∀ N : Subgroup pi.ker, N.Normal →
      ∃ x : Fin 1 → pi.ker, Subgroup.normalClosure (Set.range x) = N :=
    normal_generating_tuples_of_surjective e.symm.toMonoidHom e.symm.surjective
      (PrimitiveSixFinalPublishedNormalGenerators.normal_generating_singletons socle catalogue f.range)
  exact normal_generating_tuples_cyclic_extension pi hpi hK

theorem quotientSocle_two
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence)
    {G Q : Type} [Group G] [Group Q] [Finite Q] [IsCyclic Q]
    (pi : G →* Q) (hpi : Function.Surjective pi)
    (f : pi.ker →* Equiv.Perm (Fin 6)) (hf : Function.Injective f)
    [MulAction.IsPreprimitive f.range (Fin 6)]
    (N : Subgroup G) [N.Normal] : SocleNormalGeneratorBound (G ⧸ N) 2 :=
  quotientSocleNormalGeneratorBound_of_normal_generating_tuples
    (normal_pairs socle catalogue pi hpi f hf) N

end SymmetricSubgroupAsymptotics.PrimitiveSixKernelCyclicExtension
