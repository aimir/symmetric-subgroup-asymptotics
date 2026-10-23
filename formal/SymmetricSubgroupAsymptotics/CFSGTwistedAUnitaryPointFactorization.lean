import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryFieldGeometry
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryOpposedFixedRealization

/-! Reinsert the already constructed common field component after a
literal linear point realization. This intermediate composition lemma
retains its realization premise explicitly; concrete parity consumers
discharge it rather than exposing a new model-recognition input. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists CFSGHermitianOrthogonalSpan
open CFSGHermitianSimilitudeGroup CFSGProjectiveFieldAction

local instance (q : CFSG.PrimePower) (tau : q.Extension 2 ≃+* q.Extension 2) :
    RingHomSurjective tau.toRingHom := ⟨tau.surjective⟩
local instance (q : CFSG.PrimePower) (tau : q.Extension 2 ≃+* q.Extension 2) :
    RingHomInvPair tau.toRingHom tau.symm.toRingHom := RingHomInvPair.of_ringEquiv tau
local instance (q : CFSG.PrimePower) (tau : q.Extension 2 ≃+* q.Extension 2) :
    RingHomInvPair tau.symm.toRingHom tau.toRingHom := RingHomInvPair.of_ringEquiv_symm tau

theorem unitaryFieldPointEquiv_submodule (q : CFSG.PrimePower) (r : ℕ)
    (tau : q.Extension 2 ≃+* q.Extension 2) (R : UnitaryPoint q r) :
    (unitaryFieldPointEquiv q r tau R).val = R.val.map (coordinateEquiv tau).toLinearMap := rfl

theorem unitary_field_linear_factor_of_point_realization (q : CFSG.PrimePower) (s : ℕ)
    (hrealize : ∀ p : Equiv.Perm (UnitaryPoint q (s+3)),
      PreservesOrthogonality (definingFieldAutomorphism q 2)
        (signedReversalUnit (q.Extension 2) (s+3) : Mat (q.Extension 2) (s+3)) p →
      UnitaryLinearPointPieces q (s+3) p →
      ∃ g : similitudes (definingFieldAutomorphism q 2) (signedReversalUnit (q.Extension 2) (s+3)),
        ∀ R : UnitaryPoint q (s+3), p R =
          singularPointHom (definingFieldAutomorphism q 2) (signedReversalUnit (q.Extension 2) (s+3)) g R)
    (f : MulAut (CFSG.Models.TwistedA (s+3) q)) :
    ∃ (tau : q.Extension 2 ≃+* q.Extension 2)
      (g : similitudes (definingFieldAutomorphism q 2) (signedReversalUnit (q.Extension 2) (s+3))),
      ∀ R : UnitaryPoint q (s+3), ((unitaryOrthogonalityActionHom q s f).val R).val =
        (R.val.map g.val.toLinearMap).map (coordinateEquiv tau).toLinearMap := by
  obtain ⟨tau,htau⟩ := unitary_exists_field_normalized_linear_pieces q s f
  let p := (unitaryOrthogonalityActionHom q s f).val
  let rho := unitaryFieldPointEquiv q (s+3) tau
  let p₀ := p.trans rho.symm
  have hp₀ : PreservesOrthogonality (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) (s+3) : Mat (q.Extension 2) (s+3)) p₀ :=
    CFSGHermitianFieldAction.normalized_orthogonality (definingFieldAutomorphism q 2) tau
      (signedReversalUnit (q.Extension 2) (s+3) : Mat (q.Extension 2) (s+3))
      (unitary_definingField_commute q tau) (map_signedReversalUnit_val tau.toRingHom (s+3))
      p (unitaryOrthogonalityActionHom q s f).property
  obtain ⟨g,hg⟩ := hrealize p₀ hp₀ htau
  refine ⟨tau,g,?_⟩
  intro R
  have hcancel : rho (p₀ R) = p R := rho.apply_symm_apply (p R)
  have he : p R = rho (singularPointHom (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) (s+3)) g R) :=
    hcancel.symm.trans (congrArg rho (hg R))
  have hv := congrArg (fun T : UnitaryPoint q (s+3) => T.val) he
  change ((unitaryOrthogonalityActionHom q s f).val R).val =
    (unitaryFieldPointEquiv q (s+3) tau
      (singularPointHom (definingFieldAutomorphism q 2) (signedReversalUnit (q.Extension 2) (s+3)) g R)).val at hv
  rw [unitaryFieldPointEquiv_submodule,singularPointHom_val] at hv
  exact hv

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
