import SymmetricSubgroupAsymptotics.PrimitiveCatalogueClassificationAssembly
import SymmetricSubgroupAsymptotics.PrimitiveBoundedCataloguePublishedLocator

/-!
# Primitive catalogue classification from published inputs

The former `PreE7PrimitiveCatalogueClassificationInput` bundled two quite
different facts.  The first is the affine/nonaffine socle dichotomy for a
finite faithful primitive action, in its standard O'Nan--Scott form.  The
second is the bounded almost-simple lookup after the analytic outer-order
inequality has failed.  Lean already proves that this second branch has
degree below thirty and kernel-checks exact action/socle orders and the
numerical inequality on all 116 retained rows.

This file separates those published inputs and proves that they imply the
former monolithic interface.  The finite correspondence is the degree
`5`--`29` slice of Roney-Dougal's classification of primitive permutation
groups of degree below 2500, as represented by PrimGrp 3.4.4.  It supplies
only the permutation-isomorphism locator and the exact action and socle
orders.  Lean obtains the quotient order by Lagrange's theorem and
`PrimitiveBoundedIndexReceipt` proves the inequality itself.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

/-- **Published O'Nan--Scott input.**  A finite faithful primitive action
has either its natural nonabelian characteristically-simple socle profile or
a regular normal elementary-abelian prime-power subgroup.  The profile used
here is the already derived outer-log version: its quotient action and the
bound `|L/E| <= 3 log₂ ell` are the standard nonaffine consequences recorded
in the primitive-socle and small-index literature.

The second field is the same theorem applied to the literal primitive
component of an actual minimal block. -/
structure PublishedPrimitiveSocleDichotomyInput where
  primitive : ∀ w (U : PreE7NonPairActionClass w), 5 ≤ w →
    MulAction.IsPreprimitive (preE7NonPairAction w U) (Fin w) →
    ExactPrimitiveSemisimpleOuterLogProfile
        (preE7NonPairAction w U) w ⊕
      PrimitiveAffineProfile (preE7NonPairAction w U) (Fin w)
  imprimitive : ∀ w (U : PreE7NonPairActionClass w), 5 ≤ w →
    (basePoint : Fin w) →
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint) →
    ExactPrimitiveSemisimpleOuterLogProfile block.Component
        (Nat.card block.Fibre) ⊕
      PrimitiveAffineProfile block.Component block.Fibre

/-- **Published bounded primitive-catalogue correspondence.**

This is the general finite-action statement from
`PrimitiveBoundedCataloguePublishedLocator`, rather than an alias for the
project's desired `PreE7PrimitiveCatalogueMatchData`.  Its output contains a
PrimGrp row and only the exact orders of the literal action and its actual
socle. -/
def PublishedBoundedPrimitiveCatalogueCorrespondence : Prop :=
  PublishedBoundedPrimitiveCatalogueClassification

/-- The two published classification inputs imply the former combined
primitive classification interface.  Direct profiles never touch the finite
catalogue; a catalogue row is requested only after Lean has proved the
degree-`<30` reduction. -/
noncomputable def preE7PrimitiveCatalogueClassificationInput_of_published
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence) :
    PreE7PrimitiveCatalogueClassificationInput where
  primitive := by
    intro w U hw hp
    exact match socle.primitive w U hw hp with
    | .inr affine => .inr affine
    | .inl exactProfile => .inl
        { profile := exactProfile.profile
          boundedMatch := by
            intro hone hsmall
            by_cases hdirect : 2 * exactProfile.profile.outerOrder ≤ w
            · exact .direct hdirect
            · have hdegree :=
                _root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveSemisimpleOuterLogProfile.degree_lt_thirty_of_index_failure
                    exactProfile.profile
                    hone hsmall hdirect
              letI : MulAction.IsPreprimitive
                  (preE7NonPairAction w U) (Fin w) := hp
              letI : Nontrivial (Fin w) :=
                Fin.nontrivial_iff_two_le.mpr (by omega)
              have hcatalogue :
                  PublishedBoundedPrimitiveCatalogueClassification := catalogue
              let locator := Classical.choice (hcatalogue
                (preE7NonPairAction w U) (Fin w) exactProfile.profile.E
                exactProfile.profile.chart
                (by simpa using hw) (by simpa using hdegree)
                (exactProfile.oneFactor_socle_nontrivial hone)
                (exactProfile.oneFactor_socle_le hone)
                (exactProfile.factorCount_eq_chart.symm.trans hone))
              exact .catalogue
                (exactProfile.profileMatch hone (by simp) locator) }
  imprimitive := by
    intro w U hw basePoint block
    exact match socle.imprimitive w U hw basePoint block with
    | .inr affine => .inr affine
    | .inl exactProfile => .inl
        { profile := exactProfile.profile
          boundedMatch := by
            intro hone hsmall
            by_cases hdirect :
                2 * exactProfile.profile.outerOrder ≤ Nat.card block.Fibre
            · exact .direct hdirect
            · have hdegree :=
                _root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveSemisimpleOuterLogProfile.degree_lt_thirty_of_index_failure
                    exactProfile.profile
                    hone hsmall hdirect
              letI : Nontrivial block.Fibre :=
                Finite.one_lt_card_iff_nontrivial.mp
                  (show 1 < Nat.card block.Fibre by
                    have := block.degrees_ge_two.1
                    omega)
              letI : MulAction.IsPreprimitive block.Component block.Fibre :=
                block.component_preprimitive
              have hcatalogue :
                  PublishedBoundedPrimitiveCatalogueClassification := catalogue
              let locator := Classical.choice (hcatalogue
                block.Component block.Fibre exactProfile.profile.E
                exactProfile.profile.chart
                (by
                  have := exactProfile.profile.primitive_index_lower
                  simp only [hone, pow_one] at this
                  exact exactProfile.profile.leastIndex_five_le.trans this)
                hdegree (exactProfile.oneFactor_socle_nontrivial hone)
                (exactProfile.oneFactor_socle_le hone)
                (exactProfile.factorCount_eq_chart.symm.trans hone))
              exact .catalogue
                (exactProfile.profileMatch hone rfl locator) }

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
