import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairCatalogueDispatcher

/-! A source catalogue on the actual six-pair representatives. The legacy
owner table contains additional literal conjugacy/normal-registry data that
the source dispatcher never reads. Structural proofs may supply the exact
same B6 endpoint directly. Coverage remains a separate actual-class locator;
no source row or coverage proof is supplied by this interface. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

/-- Exactly182 chosen actual representatives with an actual B6 source on
each representative. No proxy action or numerical bound replaces it. -/
structure PrimitiveAffineDegreeTwoSixPairSourceTable where
  representative : Fin 182 → PreE7PairActionClass 6
  source : ∀ i, PreE7B6SourceData 12 (preE7SixPairNonPairAction (representative i))

/-- Actual catalogue coverage is separate from the complete source table.
The equality identifies the actual action-class representative, not a label. -/
def PublishedDegreeTwoSixPairSourceCatalogueLocator
    (T : PrimitiveAffineDegreeTwoSixPairSourceTable) : Prop :=
  ∀ p : PreE7PairActionClass 6, ∃ i : Fin 182, p = T.representative i

/-- The exact representative-facing boundary used by the residual source. -/
abbrev DegreeTwoSixPairRepresentativeB6Source :=
  ∀ p : PreE7PairActionClass 6, PreE7B6SourceData 12 (preE7SixPairNonPairAction p)

theorem exists_degreeTwoSixPairSource_of_sourceTable
    (T : PrimitiveAffineDegreeTwoSixPairSourceTable)
    (published : PublishedDegreeTwoSixPairSourceCatalogueLocator T)
    (p : PreE7PairActionClass 6) :
    Nonempty (PreE7B6SourceData 12 (preE7SixPairNonPairAction p)) := by
  obtain ⟨i,rfl⟩ := published p
  exact ⟨T.source i⟩

/-- Dispatch only after actual source construction and actual coverage. -/
def degreeTwoSixPairSource_of_sourceTable
    (T : PrimitiveAffineDegreeTwoSixPairSourceTable)
    (published : PublishedDegreeTwoSixPairSourceCatalogueLocator T) :
    DegreeTwoSixPairRepresentativeB6Source :=
  fun p => Classical.choice (exists_degreeTwoSixPairSource_of_sourceTable T published p)

namespace PrimitiveAffineDegreeTwoSixPairOwnerTable

/-- Forget only fields that the legacy source dispatcher does not consume. -/
def toSourceTable (T : PrimitiveAffineDegreeTwoSixPairOwnerTable) :
    PrimitiveAffineDegreeTwoSixPairSourceTable where
  representative := T.representative
  source i := (T.row i).source

@[simp] theorem toSourceTable_representative
    (T : PrimitiveAffineDegreeTwoSixPairOwnerTable) (i : Fin 182) :
    T.toSourceTable.representative i = T.representative i := rfl

@[simp] theorem toSourceTable_source
    (T : PrimitiveAffineDegreeTwoSixPairOwnerTable) (i : Fin 182) :
    T.toSourceTable.source i = (T.row i).source := rfl

/-- The old actual-class locator is preserved exactly. -/
theorem toSourceTable_locator
    (T : PrimitiveAffineDegreeTwoSixPairOwnerTable)
    (published : PublishedDegreeTwoSixPairCatalogueLocator T) :
    PublishedDegreeTwoSixPairSourceCatalogueLocator T.toSourceTable := published

theorem toSourceTable_locator_iff (T : PrimitiveAffineDegreeTwoSixPairOwnerTable) :
    PublishedDegreeTwoSixPairSourceCatalogueLocator T.toSourceTable ↔
      PublishedDegreeTwoSixPairCatalogueLocator T := Iff.rfl

end PrimitiveAffineDegreeTwoSixPairOwnerTable
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics
end
