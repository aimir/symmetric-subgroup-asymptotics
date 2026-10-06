import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockDistinctSignFaithful
import SymmetricSubgroupAsymptotics.ElementaryChartIrreducibleStructure
import SymmetricSubgroupAsymptotics.SolubleMinimalNormalDerivedTarget
import Mathlib.GroupTheory.Nilpotent

/-!
# The four-sign action as a nonsplit ternary cyclic-dual target

The signed quotient is a literal two-group, hence soluble.  The preceding
distinct-sign theorems make the correlated translation subgroup minimal and
self-centralizing.  The general nonsplit extension theorem therefore turns
the original degree-twelve action into a ternary derived cyclic target.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

/-- The binary fixed chart transports its two-group structure back to the
actual signed quotient. -/
theorem degreeThreeFourBlock_signedQuotient_isPGroup
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action) :
    IsPGroup 2 (preE7NonPairAction w U ⧸ E block P) :=
  hbinary.of_equiv
    (degreeThreeFourBlockPairChart block P hr hs hcomponent).sourceEquiv.symm

/-- Transitivity on eight signed points makes the signed quotient
nontrivial. -/
theorem degreeThreeFourBlock_signedQuotient_nontrivial
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6) :
    Nontrivial (preE7NonPairAction w U ⧸ E block P) := by
  let C := degreeThreeFourBlockPairChart block P hr hs hcomponent
  letI : MulAction.IsPretransitive C.action (Fin (2 * 4)) := C.pretransitive
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq C.action
    (0 : Fin (2 * 4)) (1 : Fin (2 * 4))
  have hg1 : g ≠ 1 := by
    intro h
    rw [h, one_smul] at hg
    exact (by decide : (0 : Fin (2 * 4)) ≠ 1) hg
  letI : Nontrivial C.action := ⟨⟨g, 1, hg1⟩⟩
  exact C.sourceEquiv.symm.injective.nontrivial

/-- The signed quotient is soluble because it is a finite two-group. -/
theorem degreeThreeFourBlock_signedQuotient_isSolvable
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action) :
    IsSolvable (preE7NonPairAction w U ⧸ E block P) := by
  letI : Group.IsNilpotent (preE7NonPairAction w U ⧸ E block P) :=
    IsPGroup.isNilpotent (p := 2)
      (degreeThreeFourBlock_signedQuotient_isPGroup
        block P hr hs hcomponent hbinary)
  infer_instance

/-- Canonical last nonzero derived term of the actual signed quotient. -/
noncomputable def degreeThreeFourBlock_signedQuotientDerivedLength
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action) :
    SolubleDerivedLength (preE7NonPairAction w U ⧸ E block P) := by
  letI : IsSolvable (preE7NonPairAction w U ⧸ E block P) :=
    degreeThreeFourBlock_signedQuotient_isSolvable
      block P hr hs hcomponent hbinary
  exact Classical.choice (SolubleDerivedLength.nonempty
    (preE7NonPairAction w U ⧸ E block P)
    (degreeThreeFourBlock_signedQuotient_nontrivial
      block P hr hs hcomponent))

/-- In the four-sign branch the literal correlated translation intersection
is minimal normal in the original action. -/
theorem degreeThreeFourBlock_translationIntersection_minimal
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (hfour :
      (degreeThreeFourBlockSignedIsotypeProfile
        block P hr hs hcomponent).isotypeCount = 4) :
    ∀ W : Subgroup (preE7NonPairAction w U), W.Normal →
      W ≤ E block P → W = ⊥ ∨ W = E block P := by
  have hdim : Module.finrank (ZMod P.p) (chart block P).V = 1 := by
    have hdim' := (degreeThree_translation_prime_dim block P hr).2
    change Module.finrank (ZMod P.p) (chart block P).V = 1 at hdim'
    exact hdim'
  letI : Fact P.p.Prime := (chart block P).primeFact
  letI : Nontrivial (chart block P).V :=
    Module.nontrivial_of_finrank_pos (R := ZMod P.p) (by
      rw [hdim]
      decide)
  letI : Nontrivial (elementaryChart block P).V :=
    (degreeThreeFourBlockTranslationCoordinateEquiv
      block P hr hs hcomponent hbinary hfour).symm.injective.nontrivial
  exact ElementaryMinimalNormalChart.minimal_of_quotientRepresentation_irreducible
      (elementaryChart block P)
      (degreeThreeFourBlock_quotientRepresentation_irreducible
        block P hr hs hcomponent hbinary hfour)

/-- In the four-sign branch the same literal translation intersection is
self-centralizing. -/
theorem degreeThreeFourBlock_translationIntersection_selfCentralizing
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (hfour :
      (degreeThreeFourBlockSignedIsotypeProfile
        block P hr hs hcomponent).isotypeCount = 4) :
    ∀ g : preE7NonPairAction w U,
      (∀ e ∈ E block P, g * e = e * g) → g ∈ E block P :=
  ElementaryMinimalNormalChart.selfCentralizing_of_quotientRepresentation_injective
      (elementaryChart block P)
        (degreeThreeFourBlock_quotientRepresentation_injective
          block P hr hs hcomponent hbinary hfour)

/-- The original action in the four-sign branch is a literal nonsplit
ternary cyclic-dual target. -/
noncomputable def degreeThreeFourBlock_distinctSignDerivedCyclicTarget
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (hfour :
      (degreeThreeFourBlockSignedIsotypeProfile
        block P hr hs hcomponent).isotypeCount = 4) :
    DerivedHead.DerivedCyclicTarget
      (preE7NonPairAction w U) (E block P)
      (degreeThreeFourBlock_signedQuotientDerivedLength
        block P hr hs hcomponent hbinary).t P.p := by
  have hdim : Module.finrank (ZMod P.p) (chart block P).V = 1 := by
    have hdim' := (degreeThree_translation_prime_dim block P hr).2
    change Module.finrank (ZMod P.p) (chart block P).V = 1 at hdim'
    exact hdim'
  letI : Fact P.p.Prime := (chart block P).primeFact
  letI : Nontrivial (chart block P).V :=
    Module.nontrivial_of_finrank_pos (R := ZMod P.p) (by
      rw [hdim]
      decide)
  letI : Nontrivial (elementaryChart block P).V :=
    (degreeThreeFourBlockTranslationCoordinateEquiv
      block P hr hs hcomponent hbinary hfour).symm.injective.nontrivial
  exact SolubleMinimalNormalExtension.derivedCyclicTarget
    (elementaryChart block P)
    (degreeThreeFourBlock_translationIntersection_minimal
      block P hr hs hcomponent hbinary hfour)
    (degreeThreeFourBlock_translationIntersection_selfCentralizing
      block P hr hs hcomponent hbinary hfour)
    (degreeThreeFourBlock_signedQuotientDerivedLength
      block P hr hs hcomponent hbinary)

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
