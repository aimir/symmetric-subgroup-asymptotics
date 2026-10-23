import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryOpposedPointAlignment
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryPointFactorComposition
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryOpposedFixedRealization

/-! Normalize arbitrary actual target ranges to pointwise fixation of
the two ORIGINAL coordinate halves, transporting all local linear
pieces and orthogonality explicitly. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists CFSGHermitianOrthogonalSpan
open CFSGHermitianSimilitudeGroup

theorem exists_unitary_opposed_normalization (q : CFSG.PrimePower) (s : ℕ)
    (f : Equiv.Perm (UnitaryPoint q (s+3)))
    (hf : PreservesOrthogonality (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) (s+3) : Mat (q.Extension 2) (s+3)) f)
    (hlinear : UnitaryLinearPointPieces q (s+3) f) :
    ∃ g : similitudes (definingFieldAutomorphism q 2) (signedReversalUnit (q.Extension 2) (s+3)),
      PreservesOrthogonality (definingFieldAutomorphism q 2)
        (signedReversalUnit (q.Extension 2) (s+3) : Mat (q.Extension 2) (s+3))
        (unitarySimilitudePostcompose q (s+3) g f) ∧
      UnitaryLinearPointPieces q (s+3) (unitarySimilitudePostcompose q (s+3) g f) ∧
      (∀ R : UnitaryPoint q (s+3), R.val ≤ unitaryStandardSingularSpace q (s+3) →
        unitarySimilitudePostcompose q (s+3) g f R = R) ∧
      ∀ R : UnitaryPoint q (s+3), R.val ≤ unitaryOppositeSingularSpace q (s+3) →
        unitarySimilitudePostcompose q (s+3) g f R = R := by
  obtain ⟨g,hP,hZ⟩ := exists_unitary_opposed_point_alignment q (s+3) (by omega) f hf hlinear
  refine ⟨g,unitarySimilitudePostcompose_preserves q (s+3) g f hf,?_,?_,?_⟩
  · intro M
    obtain ⟨F⟩ := hlinear M
    exact ⟨unitarySimilitudePostcompose_piece q (s+3) g f ⟨M.val,M.property.1⟩ F⟩
  · intro R hR
    apply (singularPointHom (definingFieldAutomorphism q 2) (signedReversalUnit (q.Extension 2) (s+3)) g).injective
    exact (unitarySimilitudePostcompose_cancel q (s+3) g f R).trans (hP R hR).symm
  · intro R hR
    apply (singularPointHom (definingFieldAutomorphism q 2) (signedReversalUnit (q.Extension 2) (s+3)) g).injective
    exact (unitarySimilitudePostcompose_cancel q (s+3) g f R).trans (hZ R hR).symm

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
