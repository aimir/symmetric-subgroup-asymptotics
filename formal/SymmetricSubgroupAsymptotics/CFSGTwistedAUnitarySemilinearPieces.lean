import SymmetricSubgroupAsymptotics.CFSGHermitianSemilinearPiece
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryIsotropicSpaceAction
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryStandardCoordinates

/-! Actual original unitary automorphisms have constructed semilinear
representatives on every singular subspace of dimension at least three.
The full maximal-separation premise is discharged here from the natural
unitary action; no polar recognition hypothesis remains in this step. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists CFSGHermitianOrthogonalSpan

theorem unitary_exists_semilinearPiece (q : CFSG.PrimePower) (s : ℕ)
    (f : MulAut (CFSG.Models.TwistedA (s + 3) q))
    (S : IsotropicSpace (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) (s + 3) : Mat (q.Extension 2) (s + 3)))
    (d : ℕ) (hd : Module.finrank (q.Extension 2) S.val = d + 3) :
    ∃ tau : q.Extension 2 ≃+* q.Extension 2,
      Nonempty (SemilinearPiece (definingFieldAutomorphism q 2)
        (signedReversalUnit (q.Extension 2) (s + 3) : Mat (q.Extension 2) (s + 3))
        (unitaryOrthogonalityActionHom q s f).val S tau) :=
  exists_semilinearPiece _ _
    (fun T => unitary_isotropic_separated_by_maximal q (s + 3) T.val T.property)
    (unitaryOrthogonalityActionHom q s f).val (unitaryOrthogonalityActionHom q s f).property S d hd

theorem unitary_standard_exists_semilinearPiece (q : CFSG.PrimePower) (s : ℕ)
    (f : MulAut (CFSG.Models.TwistedA (s + 5) q)) :
    ∃ tau : q.Extension 2 ≃+* q.Extension 2,
      Nonempty (SemilinearPiece (definingFieldAutomorphism q 2)
        (signedReversalUnit (q.Extension 2) (s + 5) : Mat (q.Extension 2) (s + 5))
        (unitaryOrthogonalityActionHom q (s + 2) f).val
        ⟨unitaryStandardSingularSpace q (s + 5), unitaryStandardSingularSpace_pair_zero q (s + 5)⟩ tau) := by
  apply unitary_exists_semilinearPiece q (s + 2) f _ (((s + 6) / 2) - 3)
  change Module.finrank (q.Extension 2) (unitaryStandardSingularSpace q (s + 5)) = _
  rw [unitaryStandardSingularSpace_finrank]
  omega

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
