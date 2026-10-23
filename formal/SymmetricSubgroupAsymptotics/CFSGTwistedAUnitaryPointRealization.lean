import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryEvenPointRealization
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryOddNormalizedRealization

/-! Full point realization in EVERY original unitary natural dimension
at least four. Both parity engines are proved on the original signed
coordinates; the global statement has no geometric callback. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists CFSGHermitianOrthogonalSpan
open CFSGHermitianSimilitudeGroup

theorem exists_unitary_odd_point_realization (q : CFSG.PrimePower) (m : ℕ)
    (f : Equiv.Perm (UnitaryOddPoint q m))
    (hf : PreservesOrthogonality (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) (2*m+4) : Mat (q.Extension 2) (2*m+4)) f)
    (hlinear : UnitaryLinearPointPieces q (2*m+4) f) :
    ∃ g : similitudes (definingFieldAutomorphism q 2) (signedReversalUnit (q.Extension 2) (2*m+4)),
      ∀ R : UnitaryOddPoint q m, f R = singularPointHom (definingFieldAutomorphism q 2)
        (signedReversalUnit (q.Extension 2) (2*m+4)) g R := by
  obtain ⟨g₀,hf₀,hl₀,hP₀,hZ₀⟩ := exists_unitary_opposed_normalization q (2*m+1) f hf hlinear
  let f₀ := unitarySimilitudePostcompose q (2*m+4) g₀ f
  obtain ⟨g₁,hP₁,hZ₁,hM₁⟩ := exists_unitary_mixed_normalization q (2*m+1) f₀ hf₀ hl₀ hP₀ hZ₀
  have hl₁ : UnitaryLinearPointPieces q (2*m+4)
      (unitarySimilitudePostcompose q (2*m+4) g₁ f₀) := by
    intro M
    obtain ⟨F⟩ := hl₀ M
    exact ⟨unitarySimilitudePostcompose_piece q (2*m+4) g₁ f₀ ⟨M.val,M.property.1⟩ F⟩
  apply unitary_point_factor_of_postcompose q (2*m+4) g₀ f
  apply unitary_point_factor_of_postcompose q (2*m+4) g₁ f₀
  exact exists_unitary_odd_normalized_point_realization q m
    (unitarySimilitudePostcompose q (2*m+4) g₁ f₀)
    (unitarySimilitudePostcompose_preserves q (2*m+4) g₁ f₀ hf₀) hl₁ hP₁ hZ₁ hM₁

theorem exists_unitary_point_realization (q : CFSG.PrimePower) (s : ℕ)
    (f : Equiv.Perm (UnitaryPoint q (s+3)))
    (hf : PreservesOrthogonality (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) (s+3) : Mat (q.Extension 2) (s+3)) f)
    (hlinear : UnitaryLinearPointPieces q (s+3) f) :
    ∃ g : similitudes (definingFieldAutomorphism q 2) (signedReversalUnit (q.Extension 2) (s+3)),
      ∀ R : UnitaryPoint q (s+3), f R = singularPointHom (definingFieldAutomorphism q 2)
        (signedReversalUnit (q.Extension 2) (s+3)) g R := by
  rcases Nat.even_or_odd s with hs | hs
  · apply exists_unitary_even_point_realization q s ?_ f hf hlinear
    obtain ⟨k,hk⟩ := hs
    exact ⟨k+1,by omega⟩
  · obtain ⟨m,hm⟩ := hs
    have he : s = 2*m+1 := by omega
    subst s
    exact exists_unitary_odd_point_realization q m f hf hlinear

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
