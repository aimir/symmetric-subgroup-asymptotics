import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryPlaneSemilinearity
import SymmetricSubgroupAsymptotics.CFSGHermitianLocalFieldCoherence
import SymmetricSubgroupAsymptotics.CFSGHermitianMaximalGallery

/-! The actual rank3/4 root-star reconstruction installs the SAME
generic SemilinearPiece interface used by the higher-rank projective
restriction engine. All maximal planes are included, with no supplied
local fundamental-theorem premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped LinearAlgebra.Projectivization

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists CFSGHermitianOrthogonalSpan
local instance {K : Type*} [Field K] (tau : K ≃+* K) :
    RingHomInvPair tau.toRingHom tau.symm.toRingHom := RingHomInvPair.of_ringEquiv tau
local instance {K : Type*} [Field K] (tau : K ≃+* K) :
    RingHomInvPair tau.symm.toRingHom tau.toRingHom := RingHomInvPair.of_ringEquiv_symm tau

theorem exists_unitary_lowRank_semilinearPiece (q : CFSG.PrimePower) (s : ℕ) (hs : s ≤ 1)
    (f : MulAut (CFSG.Models.TwistedA (s + 3) q))
    (S : MaximalSpace (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) (s + 3) : Mat (q.Extension 2) (s + 3))) :
    ∃ theta : q.Extension 2 ≃+* q.Extension 2,
      Function.Commute (definingFieldAutomorphism q 2) theta ∧
      Nonempty (SemilinearPiece (definingFieldAutomorphism q 2)
        (signedReversalUnit (q.Extension 2) (s + 3) : Mat (q.Extension 2) (s + 3))
        (unitaryOrthogonalityActionHom q s f).val ⟨S.val, S.property.1⟩ theta) := by
  obtain ⟨theta, htheta, M, hM, hR⟩ := exists_unitary_maximal_plane_semilinear q s hs f S
  refine ⟨theta, htheta, ⟨⟨M, hM, ?_⟩⟩⟩
  intro x hx
  let T : IsotropicSpace (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) (s + 3) : Mat (q.Extension 2) (s + 3)) :=
    ⟨S.val, S.property.1⟩
  let R := projectiveInside (definingFieldAutomorphism q 2)
    (signedReversalUnit (q.Extension 2) (s + 3) : Mat (q.Extension 2) (s + 3)) T
    (Projectivization.mk (q.Extension 2) x hx)
  let P : unitarySingularPoints q s := (unitaryHermitianSingularPointEquiv q s).symm R.val
  have hP : P.val = (q.Extension 2) ∙ x.val :=
    projectiveInside_mk_submodule (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) (s + 3) : Mat (q.Extension 2) (s + 3)) T x hx
  have hr := hR x hx P hP
  change (q.Extension 2) ∙ M x = (unitarySingularPointActionHom q s f P).val
  exact hr.symm

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
