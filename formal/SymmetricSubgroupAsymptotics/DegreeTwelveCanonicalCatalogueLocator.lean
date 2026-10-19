import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogue
import SymmetricSubgroupAsymptotics.BinaryPairFrameTransport
import SymmetricSubgroupAsymptotics.PermutationConjugateTopChart

/-! Bare transitive degree-twelve classification supplies only point
conjugacy into the fixed 301 literal permutation groups. Reindexing the
actual original pair frame by that conjugating permutation then constructs
the project locator's group and natural-module correspondence.

The classification proposition below mentions no original pair action,
normal registry, module registry, capacity, source or numerical bound. Its
family is pinned to the literal action alphabets of the existing 301 rows. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer.DegreeTwelveCanonicalCatalogueLocator

/-- Ordinary completeness of the fixed transitive degree-twelve list,
expressed solely as conjugacy of actual point-permutation subgroups. -/
def PublishedClassification : Prop :=
  ∀ T : Subgroup (Equiv.Perm (Fin 12)),
    MulAction.IsPretransitive T (Fin 12) →
      ∃ (j : Fin 301) (g : Equiv.Perm (Fin 12)),
        MulAut.conj g • T = (DegreeTwoTwelvePairFiniteCatalogue.catalogue.row j).finite.top

variable {s : ℕ} {p : PreE7PairActionClass s}
  (F : BinaryPairFrame (preE7PairAction s p) (Fin s))
  (D : DegreeTwoPairTopFiniteInterface s) (g : Equiv.Perm (Fin s))
  (h : MulAut.conj g • F.top.range=D.top)

include h in
 theorem reindexed_range : (F.reindex g).top.range=D.top := by
  change (g.permCongrHom.toMonoidHom.comp F.top).range=D.top
  rw [MonoidHom.range_comp]
  calc
    F.top.range.map g.permCongrHom.toMonoidHom = MulAut.conj g • F.top.range := by
      rw [Subgroup.pointwise_smul_def]
      congr 1
    _ = D.top := h

/-- The same original action is retained. Only its pair labels are
conjugated, so the natural binary module agrees definitionally. -/
def realization : DegreeTwoPairTopRealization D p where
  frame := F.reindex g
  topEquiv := MulEquiv.subgroupCongr (reindexed_range F D g h).symm
  module_action_eq := by intro u v; rfl

/-- The old project-facing locator is a theorem from bare point-conjugacy
classification; no realization-valued classification callback remains. -/
theorem locator (published : PublishedClassification) :
    PublishedDegreeTwoTwelvePairTopCatalogueLocator
      DegreeTwoTwelvePairFiniteCatalogue.catalogue := by
  intro p
  let F := preE7PairFrame 12 p
  letI : MulAction.IsPretransitive F.top.range (Fin 12) := F.top_pretransitive
  obtain ⟨j,g,h⟩ := published F.top.range inferInstance
  exact ⟨j,⟨realization F (DegreeTwoTwelvePairFiniteCatalogue.catalogue.row j).finite g h⟩⟩

end PrimitiveAffineImprimitiveBlockTransfer.DegreeTwelveCanonicalCatalogueLocator
end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
