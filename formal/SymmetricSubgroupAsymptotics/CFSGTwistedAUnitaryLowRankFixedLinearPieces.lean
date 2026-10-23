import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryLowRankGlobalField
import SymmetricSubgroupAsymptotics.CFSGHermitianFixedLinearRestriction

/-! Fixing every point of the literal standard plane forces the
constructed global field component to be the identity in ranks three
and four. All maximal-plane representatives are consequently linear. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists CFSGHermitianOrthogonalSpan

theorem unitary_lowRank_fixed_standard_linear_pieces (q : CFSG.PrimePower) (s : ℕ) (hs : s ≤ 1)
    (f : MulAut (CFSG.Models.TwistedA (s + 3) q))
    (hfix : ∀ R : SingularPoint (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) (s + 3) : Mat (q.Extension 2) (s + 3)),
      R.val ≤ unitaryStandardSingularSpace q (s + 3) →
        (unitaryOrthogonalityActionHom q s f).val R = R) :
    ∀ S : MaximalSpace (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) (s + 3) : Mat (q.Extension 2) (s + 3)),
      Nonempty (unitaryLocalSemilinearPiece q s f ⟨S.val, S.property.1⟩
        (RingEquiv.refl (q.Extension 2))) := by
  obtain ⟨tau, _, htau⟩ := unitary_lowRank_exists_common_maximal_field_component q s hs f
  let E := unitaryStandardMaximalSpace q (s + 3)
  obtain ⟨F⟩ := htau E
  have hid : tau = RingEquiv.refl (q.Extension 2) :=
    semilinearPiece_field_eq_id_of_fixed_subspace _ _
      (unitaryOrthogonalityActionHom q s f).val ⟨E.val, E.property.1⟩ tau F
      (by
        change 2 ≤ Module.finrank (q.Extension 2) (unitaryStandardSingularSpace q (s + 3))
        rw [unitaryStandardSingularSpace_finrank]
        omega)
      hfix
  rw [hid] at htau
  exact htau

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
