import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryOpposedNormalization
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryMixedNormalizationAllRank
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryEvenPointDetermination

/-! Full ambient realization in EVERY even original unitary vector
dimension. Arbitrary opposed target ranges, the common mixed ratio and
the final pointwise kernel are all discharged by checked constructions.
There is no residual geometric callback in this theorem. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists CFSGHermitianOrthogonalSpan
open CFSGHermitianSimilitudeGroup

theorem exists_unitary_even_point_realization (q : CFSG.PrimePower) (s : ℕ) (hr : Odd (s+3))
    (f : Equiv.Perm (UnitaryPoint q (s+3)))
    (hf : PreservesOrthogonality (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) (s+3) : Mat (q.Extension 2) (s+3)) f)
    (hlinear : UnitaryLinearPointPieces q (s+3) f) :
    ∃ g : similitudes (definingFieldAutomorphism q 2) (signedReversalUnit (q.Extension 2) (s+3)),
      ∀ R : UnitaryPoint q (s+3), f R =
        singularPointHom (definingFieldAutomorphism q 2) (signedReversalUnit (q.Extension 2) (s+3)) g R := by
  obtain ⟨g₀,hf₀,hl₀,hP₀,hZ₀⟩ := exists_unitary_opposed_normalization q s f hf hlinear
  let f₀ := unitarySimilitudePostcompose q (s+3) g₀ f
  obtain ⟨g₁,hP₁,hZ₁,hM₁⟩ := exists_unitary_mixed_normalization q s f₀ hf₀ hl₀ hP₀ hZ₀
  have hfix := unitary_even_point_determination q s hr
    (unitarySimilitudePostcompose q (s+3) g₁ f₀)
    (unitarySimilitudePostcompose_preserves q (s+3) g₁ f₀ hf₀) hP₁ hZ₁ hM₁
  apply unitary_point_factor_of_postcompose q (s+3) g₀ f
  apply unitary_point_factor_of_postcompose q (s+3) g₁ f₀
  refine ⟨1,?_⟩
  intro R
  rw [map_one]
  exact hfix R

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
