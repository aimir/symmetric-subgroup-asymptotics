import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryIsotropicSubspaceNormalization
import SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! Actual maximal-singular-space transitivity, deduced from recursive
literal normalization. Standard-space maximality follows by dimension
comparison under an actual invertible word, rather than a supplied Witt
index. All ranks and field characteristics remain in the statements. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent
open CFSGTwistedAUnitaryParameters CFSGSerreOrdinaryTwists
open CFSGHermitianOrthogonalSpan

theorem unitarySubspaceImage_finrank (q : CFSG.PrimePower) (r : ℕ)
    (g : naturalFixed r q)
    (S : Submodule (q.Extension 2) (Fin (r + 1) → q.Extension 2)) :
    Module.finrank (q.Extension 2) (unitarySubspaceImage q r g S) =
      Module.finrank (q.Extension 2) S :=
  ((unitaryNaturalLinearEquiv q r g).submoduleMap S).finrank_eq.symm

theorem unitaryStandardSingularSpace_maximal (q : CFSG.PrimePower) (r : ℕ) :
    MaximalIsotropic (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r)
      (unitaryStandardSingularSpace q r) := by
  refine ⟨unitaryStandardSingularSpace_pair_zero q r, ?_⟩
  intro T hT hWT
  obtain ⟨g, hg⟩ := exists_unitary_subspace_normalization q r T hT
  have hle : unitarySubspaceImage q r g T ≤ unitaryStandardSingularSpace q r := by
    rintro y ⟨x, hx, rfl⟩
    exact hg x hx
  have hdim := Submodule.finrank_mono hle
  rw [unitarySubspaceImage_finrank] at hdim
  exact (Submodule.eq_of_le_of_finrank_le hWT hdim).symm

theorem exists_unitary_maximal_subspace_normalization (q : CFSG.PrimePower) (r : ℕ)
    (S : Submodule (q.Extension 2) (Fin (r + 1) → q.Extension 2))
    (hS : MaximalIsotropic (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r) S) :
    ∃ g : naturalFixed r q,
      unitarySubspaceImage q r g S = unitaryStandardSingularSpace q r := by
  obtain ⟨g, hg⟩ := exists_unitary_subspace_normalization q r S hS.1
  let W := unitaryStandardSingularSpace q r
  let T := W.comap (unitaryNaturalLinearEquiv q r g).toLinearMap
  have hT : Orthogonal (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r) T T := by
    intro x hx y hy
    have h := unitaryStandardSingularSpace_pair_zero q r
      (unitaryNaturalLinearEquiv q r g x) hx (unitaryNaturalLinearEquiv q r g y) hy
    exact (unitaryNaturalLinearEquiv_pair q r g x y).symm.trans h
  have hST : S ≤ T := by intro x hx; exact hg x hx
  have he : T = S := hS.2 T hT hST
  refine ⟨g, le_antisymm ?_ ?_⟩
  · rintro y ⟨x, hx, rfl⟩
    exact hg x hx
  · intro y hy
    let x := (unitaryNaturalLinearEquiv q r g).symm y
    have hxT : x ∈ T := by
      change unitaryNaturalLinearEquiv q r g ((unitaryNaturalLinearEquiv q r g).symm y) ∈ W
      simpa only [LinearEquiv.apply_symm_apply] using hy
    have hxS : x ∈ S := he ▸ hxT
    exact ⟨x, hxS, (unitaryNaturalLinearEquiv q r g).apply_symm_apply y⟩

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
