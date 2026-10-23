import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitarySingularPointAction
import SymmetricSubgroupAsymptotics.CFSGHermitianMaximalSubspaceHom

/-! Actual original-model unitary automorphisms act on maximal literal
signed-isotropic subspaces, with their singular-point incidence retained.
The point carrier is all singular lines, as previously proved by words. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGSerreOrdinaryTwists CFSGTwistedANaturalMatrices CFSGHermitianOrthogonalSpan

def unitaryHermitianSingularPointEquiv (q : CFSG.PrimePower) (s : ℕ) :
    unitarySingularPoints q s ≃ SingularPoint (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) (s + 3) : Mat (q.Extension 2) (s + 3)) where
  toFun P := ⟨P.val, P.property⟩
  invFun P := ⟨P.val, P.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

def unitaryOrthogonalityActionHom (q : CFSG.PrimePower) (s : ℕ) :
    MulAut (CFSG.Models.TwistedA (s + 3) q) →*
      orthogonalityGroup (definingFieldAutomorphism q 2)
        (signedReversalUnit (q.Extension 2) (s + 3) : Mat (q.Extension 2) (s + 3)) :=
  MonoidHom.codRestrict
    (((unitaryHermitianSingularPointEquiv q s).permCongrHom.toMonoidHom).comp
      (unitarySingularPointActionHom q s)) _ (by
        intro f P Q
        exact unitarySingularPointAction_preserves_orthogonality q s f
          ((unitaryHermitianSingularPointEquiv q s).symm P)
          ((unitaryHermitianSingularPointEquiv q s).symm Q))

def unitaryMaximalIsotropicActionHom (q : CFSG.PrimePower) (s : ℕ) :
    MulAut (CFSG.Models.TwistedA (s + 3) q) →*
      Equiv.Perm {S : Submodule (q.Extension 2) (Fin (s + 4) → q.Extension 2) //
        MaximalIsotropic (definingFieldAutomorphism q 2)
          (signedReversalUnit (q.Extension 2) (s + 3) : Mat (q.Extension 2) (s + 3)) S} :=
  (maximalIsotropicActionHom (definingFieldAutomorphism q 2)
    (signedReversalUnit (q.Extension 2) (s + 3) : Mat (q.Extension 2) (s + 3))).comp
      (unitaryOrthogonalityActionHom q s)

theorem unitaryMaximalIsotropicAction_incidence (q : CFSG.PrimePower) (s : ℕ)
    (f : MulAut (CFSG.Models.TwistedA (s + 3) q))
    (S : {S : Submodule (q.Extension 2) (Fin (s + 4) → q.Extension 2) //
      MaximalIsotropic (definingFieldAutomorphism q 2)
        (signedReversalUnit (q.Extension 2) (s + 3) : Mat (q.Extension 2) (s + 3)) S})
    (P : unitarySingularPoints q s) :
    (unitarySingularPointActionHom q s f P).val ≤ (unitaryMaximalIsotropicActionHom q s f S).val ↔
      P.val ≤ S.val :=
  maximalIsotropicActionHom_incidence (definingFieldAutomorphism q 2)
    (signedReversalUnit (q.Extension 2) (s + 3) : Mat (q.Extension 2) (s + 3))
      (unitaryOrthogonalityActionHom q s f) S (unitaryHermitianSingularPointEquiv q s P)

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
