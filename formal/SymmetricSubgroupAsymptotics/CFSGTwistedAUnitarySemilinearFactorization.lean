import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryPointRealization
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryPointFactorization

/-! The SAME original twisted-A automorphism action factors through an
actual signed-form similitude and an automorphism of its SAME quadratic
defining field, in every rank at least three and every characteristic.
There is no residual geometric, alignment or middle-action premise. -/
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

theorem unitary_exists_field_linear_factor (q : CFSG.PrimePower) (s : ℕ)
    (f : MulAut (CFSG.Models.TwistedA (s+3) q)) :
    ∃ (tau : q.Extension 2 ≃+* q.Extension 2)
      (g : similitudes (definingFieldAutomorphism q 2) (signedReversalUnit (q.Extension 2) (s+3))),
      ∀ R : UnitaryPoint q (s+3), ((unitaryOrthogonalityActionHom q s f).val R).val =
        (R.val.map g.val.toLinearMap).map (coordinateEquiv tau).toLinearMap :=
  unitary_field_linear_factor_of_point_realization q s (exists_unitary_point_realization q s) f

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
