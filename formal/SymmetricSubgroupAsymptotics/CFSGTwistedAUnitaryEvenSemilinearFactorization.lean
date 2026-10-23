import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryEvenPointRealization
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryPointFactorization

/-! Callback-free geometric factorization of the SAME original
twisted-A automorphism action in every even vector dimension. The
actual common field component and ambient similitude are constructed. -/
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

theorem unitary_even_exists_field_linear_factor (q : CFSG.PrimePower) (s : ℕ) (hr : Odd (s+3))
    (f : MulAut (CFSG.Models.TwistedA (s+3) q)) :
    ∃ (tau : q.Extension 2 ≃+* q.Extension 2)
      (g : similitudes (definingFieldAutomorphism q 2) (signedReversalUnit (q.Extension 2) (s+3))),
      ∀ R : UnitaryPoint q (s+3), ((unitaryOrthogonalityActionHom q s f).val R).val =
        (R.val.map g.val.toLinearMap).map (coordinateEquiv tau).toLinearMap :=
  unitary_field_linear_factor_of_point_realization q s
    (exists_unitary_even_point_realization q s hr) f

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
