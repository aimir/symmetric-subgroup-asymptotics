import SymmetricSubgroupAsymptotics.PrimitiveCatalogueClassificationAssembly

/-!
# Primitive catalogue classification from published inputs

The former `PreE7PrimitiveCatalogueClassificationInput` bundled two quite
different facts.  The first is the affine/nonaffine socle dichotomy for a
finite faithful primitive action, in its standard O'Nan--Scott form.  The
second is the bounded almost-simple lookup after the analytic outer-order
inequality has failed.  Lean already proves that this second branch has
degree below thirty and kernel-checks the numerical inequality on all 116
retained rows.

This file separates those published inputs and proves that they imply the
former monolithic interface.  The finite correspondence is the degree
`5`--`29` slice of Roney-Dougal's classification of primitive permutation
groups of degree below 2500, as represented by PrimGrp 3.4.4.  It supplies
only the permutation-isomorphism locator and the resulting socle-quotient
order equality; `PrimitiveBoundedIndexReceipt` proves the inequality itself.
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
    PrimitiveSemisimpleOuterLogProfile
        (preE7NonPairAction w U) w ⊕
      PrimitiveAffineProfile (preE7NonPairAction w U) (Fin w)
  imprimitive : ∀ w (U : PreE7NonPairActionClass w), 5 ≤ w →
    (basePoint : Fin w) →
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint) →
    PrimitiveSemisimpleOuterLogProfile block.Component
        (Nat.card block.Fibre) ⊕
      PrimitiveAffineProfile block.Component block.Fibre

/-- **Published bounded primitive-catalogue correspondence.**

After the one-factor, least-index-below-thirty profile fails the direct
inequality, `degree_lt_thirty_of_index_failure` proves that its action degree
is below thirty.  Roney-Dougal's published classification and the pinned
PrimGrp representative table then identify the action with one of the 116
rows in `PrimitiveBoundedIndexReceipt`.  The two displayed equalities are
exactly the isomorphism-invariant data used by Lean; no normal-subgroup or
counting conclusion is imported from the catalogue. -/
abbrev PublishedBoundedPrimitiveCatalogueCorrespondence :=
  PreE7PrimitiveCatalogueMatchData

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
    | .inl profile => .inl
        { profile := profile
          boundedMatch := by
            intro hone hsmall
            by_cases hdirect : 2 * profile.outerOrder ≤ w
            · exact .direct hdirect
            · exact .catalogue
                (catalogue.primitive w U hw hp profile hone hsmall hdirect) }
  imprimitive := by
    intro w U hw basePoint block
    exact match socle.imprimitive w U hw basePoint block with
    | .inr affine => .inr affine
    | .inl profile => .inl
        { profile := profile
          boundedMatch := by
            intro hone hsmall
            by_cases hdirect :
                2 * profile.outerOrder ≤ Nat.card block.Fibre
            · exact .direct hdirect
            · exact .catalogue
                (catalogue.imprimitive w U hw basePoint block profile
                  hone hsmall hdirect) }

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
