import SymmetricSubgroupAsymptotics.ChiefSeriesTransport
import SymmetricSubgroupAsymptotics.TransitiveHeadDegreeInduction

/-!
# Zero ternary chief weight in primitive degree six

The published primitive degree-six list consists of the natural groups
`A₅`, `S₅`, `A₆`, and `S₆` in their faithful primitive
six-point actions.  The standard alternating/symmetric chief series already
formalized in this project has no cyclic factor of order three.  Thus this
finite classification slice supplies a zero-weight series, rather than an
unproved numerical rank assertion.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

/-- The degree-six slice of the published primitive permutation-group
classification. -/
def PublishedPrimitiveDegreeSixClassification : Prop :=
  ∀ (G X : Type) [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [MulAction.IsPreprimitive G X] [Nontrivial X],
    Nat.card X = 6 →
      Nonempty (G ≃* alternatingGroup (Fin 5)) ∨
      Nonempty (G ≃* Equiv.Perm (Fin 5)) ∨
      Nonempty (G ≃* alternatingGroup (Fin 6)) ∨
      Nonempty (G ≃* Equiv.Perm (Fin 6))

/-- Every primitive degree-six component has a chosen actual chief series
of ternary weight zero. -/
theorem primitiveDegreeSix_chiefWeight_eq_zero
    (h6 : PublishedPrimitiveDegreeSixClassification)
    (G X : Type) [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [MulAction.IsPreprimitive G X] [Nontrivial X]
    (hdegree : Nat.card X = 6) :
    ∃ c : ActualChiefSeries G, actualChiefSeriesTernaryWeight c = 0 := by
  rcases h6 G X hdegree with hA5 | hS5 | hA6 | hS6
  · exact alternatingChiefSeries_zero_of_equiv 5 (by omega) (Classical.choice hA5)
  · exact symmetricChiefSeries_zero_of_equiv 5 (by omega) (Classical.choice hS5)
  · exact alternatingChiefSeries_zero_of_equiv 6 (by omega) (Classical.choice hA6)
  · exact symmetricChiefSeries_zero_of_equiv 6 (by omega) (Classical.choice hS6)

end SymmetricSubgroupAsymptotics

end
