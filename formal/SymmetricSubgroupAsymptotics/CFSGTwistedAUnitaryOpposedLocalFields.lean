import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryLowRankSemilinearPieces
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryOpposedPairing
import SymmetricSubgroupAsymptotics.CFSGHermitianOpposedPieceFields

/-! Original unitary automorphisms have one actual quadratic-field
component on the literal standard/opposite pair, including polar rank
two. Original nondegenerate cross-pairing forces equality of the two
constructed local components. Global coherence is a subsequent step. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists CFSGHermitianOrthogonalSpan
local instance {K : Type*} [Field K] (tau : K ≃+* K) :
    RingHomInvPair tau.toRingHom tau.symm.toRingHom := RingHomInvPair.of_ringEquiv tau
local instance {K : Type*} [Field K] (tau : K ≃+* K) :
    RingHomInvPair tau.symm.toRingHom tau.toRingHom := RingHomInvPair.of_ringEquiv_symm tau

theorem unitaryOppositeSingularSpace_maximal (q : CFSG.PrimePower) (r : ℕ) :
    MaximalIsotropic (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r)
      (unitaryOppositeSingularSpace q r) := by
  refine ⟨(fun x hx y hy => unitaryOppositeSingularSpace_pair_zero q r x y hx hy), ?_⟩
  intro T hT hZT
  obtain ⟨g, hg⟩ := exists_unitary_subspace_normalization q r T hT
  have hle : unitarySubspaceImage q r g T ≤ unitaryStandardSingularSpace q r := by
    rintro y ⟨x, hx, rfl⟩
    exact hg x hx
  have hdim := Submodule.finrank_mono hle
  rw [unitarySubspaceImage_finrank, unitaryStandardSingularSpace_finrank] at hdim
  apply (Submodule.eq_of_le_of_finrank_le hZT _).symm
  rw [unitaryOppositeSingularSpace_finrank]
  exact hdim

def unitaryStandardMaximalSpace (q : CFSG.PrimePower) (r : ℕ) :
    MaximalSpace (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r) :=
  ⟨unitaryStandardSingularSpace q r, unitaryStandardSingularSpace_maximal q r⟩

def unitaryOppositeMaximalSpace (q : CFSG.PrimePower) (r : ℕ) :
    MaximalSpace (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r) :=
  ⟨unitaryOppositeSingularSpace q r, unitaryOppositeSingularSpace_maximal q r⟩

def unitaryStandardIsotropicSpace (q : CFSG.PrimePower) (r : ℕ) :
    IsotropicSpace (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r) :=
  ⟨unitaryStandardSingularSpace q r, unitaryStandardSingularSpace_pair_zero q r⟩

def unitaryOppositeIsotropicSpace (q : CFSG.PrimePower) (r : ℕ) :
    IsotropicSpace (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r) :=
  ⟨unitaryOppositeSingularSpace q r,
    fun x hx y hy => unitaryOppositeSingularSpace_pair_zero q r x y hx hy⟩

def unitaryLocalSemilinearPiece (q : CFSG.PrimePower) (s : ℕ)
    (f : MulAut (CFSG.Models.TwistedA (s + 3) q))
    (S : IsotropicSpace (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) (s + 3) : Mat (q.Extension 2) (s + 3)))
    (theta : q.Extension 2 ≃+* q.Extension 2) : Type :=
  SemilinearPiece (definingFieldAutomorphism q 2)
    (signedReversalUnit (q.Extension 2) (s + 3) : Mat (q.Extension 2) (s + 3))
    (unitaryOrthogonalityActionHom q s f).val S theta

theorem exists_unitary_lowRank_opposed_common_field (q : CFSG.PrimePower) (s : ℕ) (hs : s ≤ 1)
    (f : MulAut (CFSG.Models.TwistedA (s + 3) q)) :
    ∃ theta : q.Extension 2 ≃+* q.Extension 2,
      Function.Commute (definingFieldAutomorphism q 2) theta ∧
      Nonempty (unitaryLocalSemilinearPiece q s f (unitaryStandardIsotropicSpace q (s + 3)) theta) ∧
      Nonempty (unitaryLocalSemilinearPiece q s f (unitaryOppositeIsotropicSpace q (s + 3)) theta) := by
  obtain ⟨tauP, hPcomm, ⟨F⟩⟩ := exists_unitary_lowRank_semilinearPiece q s hs f
    (unitaryStandardMaximalSpace q (s + 3))
  obtain ⟨tauZ, hZcomm, ⟨G⟩⟩ := exists_unitary_lowRank_semilinearPiece q s hs f
    (unitaryOppositeMaximalSpace q (s + 3))
  have hdimP : Module.finrank (q.Extension 2) (unitaryStandardSingularSpace q (s + 3)) = 2 := by
    rw [unitaryStandardSingularSpace_finrank]
    omega
  have hdimZ : Module.finrank (q.Extension 2) (unitaryOppositeSingularSpace q (s + 3)) = 2 := by
    rw [unitaryOppositeSingularSpace_finrank]
    omega
  have hND (x : unitaryStandardSingularSpace q (s + 3))
      (hx : ∀ y : unitaryOppositeSingularSpace q (s + 3),
        unitaryNaturalPair q (s + 3) x.val y.val = 0) : x = 0 := by
    apply Subtype.ext
    exact unitaryStandard_pair_opposite_nondegenerate q (s + 3) x.val x.property
      (fun y hy => hx ⟨y, hy⟩)
  have he : tauP = tauZ := semilinearPiece_fields_eq_of_opposed_planes
    (definingFieldAutomorphism q 2)
    (signedReversalUnit (q.Extension 2) (s + 3) : Mat (q.Extension 2) (s + 3))
    (unitaryOrthogonalityActionHom q s f).val (unitaryOrthogonalityActionHom q s f).property
    _ _ hdimP hdimZ hND tauP tauZ F G hZcomm
  subst tauZ
  exact ⟨tauP, hPcomm, ⟨F⟩, ⟨G⟩⟩

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
