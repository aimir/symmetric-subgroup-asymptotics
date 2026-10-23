import SymmetricSubgroupAsymptotics.CFSGHermitianIsotropicSpaceAction
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryMaximalSeparation
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryMaximalSubspaceAction

/-! Original unitary automorphisms act on the ENTIRE literal isotropic
subspace order. The separating-extension condition of the shared theorem
is discharged by the actual opposite-half dual projection and words. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists CFSGHermitianOrthogonalSpan

def unitaryIsotropicSpaceOrderIso (q : CFSG.PrimePower) (s : ℕ)
    (f : MulAut (CFSG.Models.TwistedA (s + 3) q)) :
    IsotropicSpace (definingFieldAutomorphism q 2)
        (signedReversalUnit (q.Extension 2) (s + 3) : Mat (q.Extension 2) (s + 3)) ≃o
      IsotropicSpace (definingFieldAutomorphism q 2)
        (signedReversalUnit (q.Extension 2) (s + 3) : Mat (q.Extension 2) (s + 3)) :=
  isotropicSpaceOrderIso _ _
    (fun S => unitary_isotropic_separated_by_maximal q (s + 3) S.val S.property)
    (unitaryOrthogonalityActionHom q s f).val (unitaryOrthogonalityActionHom q s f).property

theorem unitaryIsotropicSpaceOrderIso_incidence (q : CFSG.PrimePower) (s : ℕ)
    (f : MulAut (CFSG.Models.TwistedA (s + 3) q))
    (S : IsotropicSpace (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) (s + 3) : Mat (q.Extension 2) (s + 3)))
    (P : unitarySingularPoints q s) :
    (unitarySingularPointActionHom q s f P).val ≤ (unitaryIsotropicSpaceOrderIso q s f S).val ↔
      P.val ≤ S.val :=
  isotropicSpaceEquiv_incidence _ _
    (fun S => unitary_isotropic_separated_by_maximal q (s + 3) S.val S.property)
    (unitaryOrthogonalityActionHom q s f).val (unitaryOrthogonalityActionHom q s f).property
    S (unitaryHermitianSingularPointEquiv q s P)

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
