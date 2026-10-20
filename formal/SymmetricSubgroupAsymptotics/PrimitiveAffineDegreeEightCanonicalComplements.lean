import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeEightThreeImages
import SymmetricSubgroupAsymptotics.GeneralThreeTwoSmallAffineBindings
import SymmetricSubgroupAsymptotics.SmallAffineCanonicalRepresentatives

/-! Unconditional exact degree-eight slice of the fixed small-affine
complement catalogue. The other catalogue degrees16 and27 are not claimed
here. The actual image-conjugacy statement is retained in ThreeImages. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeEightCanonicalComplements

open Non2UnipotentPrefixFiniteMenu

variable {L Ω : Type} [Group L] [MulAction L Ω]
  [Finite L] [Finite Ω] [Nontrivial Ω] [FaithfulSMul L Ω]
  (P : PrimitiveAffineProfile L Ω)

theorem complement_classification
    (hprimitive : MulAction.IsPreprimitive L Ω) (x : Ω) (hdegree : Nat.card Ω = 8) :
    ∃ i : Fin 3, Nonempty
      (P.complement x ≃* (SmallAffineCanonicalRepresentatives.degreeEight i).Carrier) := by
  obtain ⟨i, ⟨e⟩⟩ := PrimitiveAffineDegreeEightThreeImages.complement_model
    P hprimitive x hdegree
  fin_cases i
  · exact ⟨0, ⟨e.trans GeneralThreeTwoSmallAffineBindings.sevenEquiv⟩⟩
  · exact ⟨1, ⟨e.trans GeneralThreeTwoSmallAffineBindings.twentyOneEquiv⟩⟩
  · exact ⟨2, ⟨e.trans GeneralThreeTwoSmallAffineBindings.fullEquiv⟩⟩

/-- Exactly the degree-eight branch of the original fixed-row locator,
with no published classification or correspondence hypothesis. -/
theorem catalogue_locator
    (hprimitive : MulAction.IsPreprimitive L Ω) (x : Ω) (hdegree : Nat.card Ω = 8) :
    ∃ r : SmallAffineCatalogueRow, r.degree = Nat.card Ω ∧
      Nonempty (P.complement x ≃*
        (SmallAffineCanonicalRepresentatives.representative r).Carrier) := by
  obtain ⟨i, e⟩ := complement_classification P hprimitive x hdegree
  exact ⟨.degreeEight i, hdegree.symm, e⟩

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeEightCanonicalComplements

end
