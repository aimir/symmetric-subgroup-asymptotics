import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryOpposedPairing
import SymmetricSubgroupAsymptotics.CFSGHermitianOpposedPointFixation

/-! Pointwise fixation of the standard singular space and stabilization
of the literal opposite force pointwise fixation of that opposite. The
nondegenerate pairing needed for the implication is proved on the actual
signed-unitary coordinates, rather than supplied as model data. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists CFSGHermitianOrthogonalSpan

theorem unitary_fixes_opposite_of_fixed_standard (q : CFSG.PrimePower) (r : ℕ)
    (f : Equiv.Perm (SingularPoint (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r)))
    (hf : PreservesOrthogonality (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r) f)
    (hfix : ∀ P : SingularPoint (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r),
      P.val ≤ unitaryStandardSingularSpace q r → f P = P)
    (hstable : ∀ P : SingularPoint (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r),
      P.val ≤ unitaryOppositeSingularSpace q r → (f P).val ≤ unitaryOppositeSingularSpace q r) :
    ∀ P : SingularPoint (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r),
      P.val ≤ unitaryOppositeSingularSpace q r → f P = P := by
  let S : IsotropicSpace (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r) :=
    ⟨unitaryStandardSingularSpace q r, unitaryStandardSingularSpace_pair_zero q r⟩
  let Z : IsotropicSpace (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r) :=
    ⟨unitaryOppositeSingularSpace q r,
      fun x hx y hy => unitaryOppositeSingularSpace_pair_zero q r x y hx hy⟩
  exact hermitian_fixes_opposite_of_pairing_nondegenerate _ _ f hf S Z
    (unitaryOpposite_pair_standard_nondegenerate q r) hfix hstable

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
