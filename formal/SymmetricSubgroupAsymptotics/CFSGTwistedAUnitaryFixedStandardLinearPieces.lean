import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryGlobalFieldComponent
import SymmetricSubgroupAsymptotics.CFSGHermitianFixedLinearRestriction

/-! In the pointwise stabilizer of the literal standard singular space,
the common field component is the identity. Every maximal singular
space therefore has a genuinely linear representative. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists CFSGHermitianOrthogonalSpan

theorem unitary_fixed_standard_linear_pieces (q : CFSG.PrimePower) (s : ℕ)
    (f : MulAut (CFSG.Models.TwistedA (s + 5) q))
    (hfix : ∀ P : SingularPoint (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) (s + 5) : Mat (q.Extension 2) (s + 5)),
      P.val ≤ unitaryStandardSingularSpace q (s + 5) →
        (unitaryOrthogonalityActionHom q (s + 2) f).val P = P) :
    ∀ S : MaximalSpace (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) (s + 5) : Mat (q.Extension 2) (s + 5)),
      Nonempty (SemilinearPiece (definingFieldAutomorphism q 2)
        (signedReversalUnit (q.Extension 2) (s + 5) : Mat (q.Extension 2) (s + 5))
        (unitaryOrthogonalityActionHom q (s + 2) f).val ⟨S.val, S.property.1⟩
        (RingEquiv.refl (q.Extension 2))) := by
  obtain ⟨tau, htau⟩ := unitary_exists_common_maximal_field_component q s f
  let E : MaximalSpace (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) (s + 5) : Mat (q.Extension 2) (s + 5)) :=
    ⟨unitaryStandardSingularSpace q (s + 5), unitaryStandardSingularSpace_maximal q (s + 5)⟩
  obtain ⟨F⟩ := htau E
  have hid : tau = RingEquiv.refl (q.Extension 2) :=
    semilinearPiece_field_eq_id_of_fixed_subspace _ _
      (unitaryOrthogonalityActionHom q (s + 2) f).val ⟨E.val, E.property.1⟩ tau F
      (by
        change 2 ≤ Module.finrank (q.Extension 2) (unitaryStandardSingularSpace q (s + 5))
        have hn := unitaryStandardSingularSpace_finrank_ge_three q (s + 5) (by omega)
        omega)
      hfix
  rw [hid] at htau
  exact htau

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
