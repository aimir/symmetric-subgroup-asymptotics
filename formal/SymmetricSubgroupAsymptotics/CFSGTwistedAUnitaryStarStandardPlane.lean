import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryStarPlaneCoordinates
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryStandardCoordinates
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryMaximalSubspaceNormalization

/-! In the two remaining polar-rank-two dimensions, the literal star
plane is the literal standard maximal singular space. Thus the checked
original-group normalization words normalize every maximal space to
the SAME plane used by coefficient reconstruction. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent CFSGSerreOrdinaryTwists
open CFSGHermitianOrthogonalSpan

theorem starPlane_le_standard (q : CFSG.PrimePower) (s : ℕ) :
    starPlane q s ≤ unitaryStandardSingularSpace q (s + 3) := by
  rintro x ⟨v, rfl⟩ i hi
  have h0 : i ≠ starPositive s 0 := by
    intro he
    have hv := congrArg (fun j : Fin (s + 4) => j.val) he
    change i.val = 0 at hv
    omega
  have h1 : i ≠ starPositive s 1 := by
    intro he
    have hv := congrArg (fun j : Fin (s + 4) => j.val) he
    change i.val = 1 at hv
    omega
  change starVector q s v i = 0
  simp only [starVector, Pi.add_apply, Pi.smul_apply, Pi.single_apply,
    if_neg h0, if_neg h1, smul_zero, add_zero]

theorem starPlane_eq_standard_of_polarRankTwo (q : CFSG.PrimePower) (s : ℕ) (hs : s ≤ 1) :
    starPlane q s = unitaryStandardSingularSpace q (s + 3) := by
  apply Submodule.eq_of_le_of_finrank_le (starPlane_le_standard q s)
  rw [unitaryStandardSingularSpace_finrank, starPlane_finrank]
  omega

theorem starPlane_maximal_of_polarRankTwo (q : CFSG.PrimePower) (s : ℕ) (hs : s ≤ 1) :
    MaximalIsotropic (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) (s + 3) : Mat (q.Extension 2) (s + 3)) (starPlane q s) := by
  rw [starPlane_eq_standard_of_polarRankTwo q s hs]
  exact unitaryStandardSingularSpace_maximal q (s + 3)

theorem exists_normalize_maximal_to_starPlane (q : CFSG.PrimePower) (s : ℕ) (hs : s ≤ 1)
    (S : Submodule (q.Extension 2) (Fin (s + 4) → q.Extension 2))
    (hS : MaximalIsotropic (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) (s + 3) : Mat (q.Extension 2) (s + 3)) S) :
    ∃ g : naturalFixed (s + 3) q, unitarySubspaceImage q (s + 3) g S = starPlane q s := by
  obtain ⟨g, hg⟩ := exists_unitary_maximal_subspace_normalization q (s + 3) S hS
  exact ⟨g, hg.trans (starPlane_eq_standard_of_polarRankTwo q s hs).symm⟩

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
