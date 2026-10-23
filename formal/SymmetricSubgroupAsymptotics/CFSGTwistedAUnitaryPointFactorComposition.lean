import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryMixedNormalization

/-! Exact cancellation and recomposition of CONSTRUCTED similitudes
on literal unitary singular points. Normalization remains at point-map
level and does not assert a new automorphism of the original group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists CFSGHermitianOrthogonalSpan
open CFSGHermitianSimilitudeGroup

theorem unitarySimilitudePostcompose_cancel (q : CFSG.PrimePower) (r : ℕ)
    (g : similitudes (definingFieldAutomorphism q 2) (signedReversalUnit (q.Extension 2) r))
    (f : Equiv.Perm (UnitaryPoint q r)) (R : UnitaryPoint q r) :
    singularPointHom (definingFieldAutomorphism q 2) (signedReversalUnit (q.Extension 2) r) g
      (unitarySimilitudePostcompose q r g f R) = f R := by
  change (singularPointHom (definingFieldAutomorphism q 2) (signedReversalUnit (q.Extension 2) r) g)
    ((singularPointHom (definingFieldAutomorphism q 2) (signedReversalUnit (q.Extension 2) r) g⁻¹) (f R)) = f R
  rw [map_inv]
  exact (singularPointHom (definingFieldAutomorphism q 2) (signedReversalUnit (q.Extension 2) r) g).apply_symm_apply (f R)

theorem unitary_point_factor_of_postcompose (q : CFSG.PrimePower) (r : ℕ)
    (g : similitudes (definingFieldAutomorphism q 2) (signedReversalUnit (q.Extension 2) r))
    (f : Equiv.Perm (UnitaryPoint q r))
    (hfactor : ∃ k : similitudes (definingFieldAutomorphism q 2) (signedReversalUnit (q.Extension 2) r),
      ∀ R : UnitaryPoint q r, unitarySimilitudePostcompose q r g f R =
        singularPointHom (definingFieldAutomorphism q 2) (signedReversalUnit (q.Extension 2) r) k R) :
    ∃ k : similitudes (definingFieldAutomorphism q 2) (signedReversalUnit (q.Extension 2) r),
      ∀ R : UnitaryPoint q r, f R =
        singularPointHom (definingFieldAutomorphism q 2) (signedReversalUnit (q.Extension 2) r) k R := by
  obtain ⟨k,hk⟩ := hfactor
  refine ⟨g*k,?_⟩
  intro R
  calc
    f R = singularPointHom (definingFieldAutomorphism q 2) (signedReversalUnit (q.Extension 2) r) g
      (unitarySimilitudePostcompose q r g f R) := (unitarySimilitudePostcompose_cancel q r g f R).symm
    _ = singularPointHom (definingFieldAutomorphism q 2) (signedReversalUnit (q.Extension 2) r) g
      (singularPointHom (definingFieldAutomorphism q 2) (signedReversalUnit (q.Extension 2) r) k R) := congrArg _ (hk R)
    _ = singularPointHom (definingFieldAutomorphism q 2) (signedReversalUnit (q.Extension 2) r) (g*k) R :=
      (congrArg (fun e : Equiv.Perm (UnitaryPoint q r) => e R)
        ((singularPointHom (definingFieldAutomorphism q 2) (signedReversalUnit (q.Extension 2) r)).map_mul g k)).symm

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
