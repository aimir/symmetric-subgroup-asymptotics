import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairSelectedWitness
import SymmetricSubgroupAsymptotics.Non2PreE7B6RankTailInstance
import SymmetricSubgroupAsymptotics.Non2PreE7PairPayload

/-!
# Checked six-pair catalogue rows and dispatcher

The finite six-pair work is emitted one physical action at a time.  This
file is the small common target for those action modules and separates two
boundaries:

* a checked literal action contains its actual pair frame, complete class
  cover, and complete normal registry;
* an owner row additionally binds that literal action to one chosen
  pre-`E7` pair representative and supplies the checked quotient certificates
  needed by the B6 source.

The final finite table will contain 182 owner rows.  Catalogue coverage is
kept as a separate published degree-twelve locator, so it cannot conceal a
missing action witness or quotient certificate.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

/-- At degree twelve every residual-pair width is arithmetically impossible,
so a six-pair representative lies canonically in the non-pair action index
used by B6. -/
def preE7SixPairNonPairAction
    (p : PreE7PairActionClass 6) : PreE7NonPairActionClass 12 :=
  ⟨p.1, fun d hd => by
    cases d <;>
      norm_num [PreE7ResidualPairCountLabel.pairCount] at hd⟩

@[simp] theorem preE7SixPairNonPairAction_literal
    (p : PreE7PairActionClass 6) :
    preE7NonPairAction 12 (preE7SixPairNonPairAction p) =
      preE7PairAction 6 p :=
  rfl

/-- One kernel-checked literal physical action.  The finite cardinalities are
fields because selected actions have different numbers of generators,
conjugacy classes, and normal states. -/
structure PrimitiveAffineDegreeTwoSixPairCheckedLiteralAction where
  G : Subgroup (Equiv.Perm (Fin 12))
  ambientCount : ℕ
  classCount : ℕ
  normalCount : ℕ
  normalGeneratorWidth : ℕ
  ambient : Fin ambientCount → G
  representative : Fin classCount → G
  stateGenerators : Fin normalCount → Fin normalGeneratorWidth → G
  checked : PrimitiveAffineDegreeTwoSixPairSelectedWitness
    G ambient representative stateGenerators

/-- One complete owner row.  The point relabelling is the literal
degree-twelve catalogue correspondence; `source` is present only after all
normal quotient rows have received their character, binary-target, or
repeated-head certificates. -/
structure PrimitiveAffineDegreeTwoSixPairOwnerRow
    (p : PreE7PairActionClass 6) where
  literal : PrimitiveAffineDegreeTwoSixPairCheckedLiteralAction
  pointRelabel : Equiv.Perm (Fin 12)
  correspondence :
    relabelSubgroup pointRelabel literal.G = preE7PairAction 6 p
  source : PreE7B6SourceData 12 (preE7SixPairNonPairAction p)

/-- The fully constructed finite table.  This contains data for every row,
but makes no catalogue-coverage assertion. -/
structure PrimitiveAffineDegreeTwoSixPairOwnerTable where
  representative : Fin 182 → PreE7PairActionClass 6
  row : ∀ i, PrimitiveAffineDegreeTwoSixPairOwnerRow (representative i)

/-- Published degree-twelve transitive-catalogue locator, restricted to
faithful transitive actions with six two-point blocks and full local `C2`.
It identifies a chosen action-class representative with a row of the
independently checked 182-row table. -/
def PublishedDegreeTwoSixPairCatalogueLocator
    (T : PrimitiveAffineDegreeTwoSixPairOwnerTable) : Prop :=
  ∀ p : PreE7PairActionClass 6, ∃ i : Fin 182, p = T.representative i

/-- The checked table and the published locator give an actual B6 source on
every six-pair representative. -/
theorem exists_degreeTwoSixPairSource
    (T : PrimitiveAffineDegreeTwoSixPairOwnerTable)
    (published : PublishedDegreeTwoSixPairCatalogueLocator T)
    (p : PreE7PairActionClass 6) :
    Nonempty (PreE7B6SourceData 12 (preE7SixPairNonPairAction p)) := by
  obtain ⟨i, rfl⟩ := published p
  exact ⟨(T.row i).source⟩

/-- Canonical dispatcher after the physical representative has been fixed.
No owner precedence or action census is used here. -/
noncomputable def degreeTwoSixPairSource
    (T : PrimitiveAffineDegreeTwoSixPairOwnerTable)
    (published : PublishedDegreeTwoSixPairCatalogueLocator T)
    (p : PreE7PairActionClass 6) :
    PreE7B6SourceData 12 (preE7SixPairNonPairAction p) :=
  Classical.choice (exists_degreeTwoSixPairSource T published p)

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
