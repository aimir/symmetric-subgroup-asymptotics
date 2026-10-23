import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryMaximalSubspaceNormalization
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryStandardCoordinates

/-! The checked literal normalization words bound EVERY isotropic
subspace dimension. In natural dimensions4/5 every pair-zero two-plane
is consequently maximal, as required by the common-opposite witness. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists CFSGHermitianOrthogonalSpan

theorem unitary_isotropic_finrank_le (q : CFSG.PrimePower) (r : ℕ)
    (S : Submodule (q.Extension 2) (Fin (r + 1) → q.Extension 2))
    (hS : ∀ x ∈ S, ∀ y ∈ S, unitaryNaturalPair q r x y = 0) :
    Module.finrank (q.Extension 2) S ≤ (r + 1) / 2 := by
  obtain ⟨g, hg⟩ := exists_unitary_subspace_normalization q r S hS
  have hle : unitarySubspaceImage q r g S ≤ unitaryStandardSingularSpace q r := by
    rintro y ⟨x, hx, rfl⟩
    exact hg x hx
  have hd := Submodule.finrank_mono hle
  simpa only [unitarySubspaceImage_finrank, unitaryStandardSingularSpace_finrank] using hd

theorem unitary_isotropic_maximal_of_finrank (q : CFSG.PrimePower) (r : ℕ)
    (S : Submodule (q.Extension 2) (Fin (r + 1) → q.Extension 2))
    (hS : ∀ x ∈ S, ∀ y ∈ S, unitaryNaturalPair q r x y = 0)
    (hd : Module.finrank (q.Extension 2) S = (r + 1) / 2) :
    MaximalIsotropic (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r) S := by
  refine ⟨hS, ?_⟩
  intro T hT hST
  apply (Submodule.eq_of_le_of_finrank_le hST _).symm
  rw [hd]
  exact unitary_isotropic_finrank_le q r T hT

theorem unitary_isotropic_plane_maximal (q : CFSG.PrimePower) (s : ℕ) (hs : s ≤ 1)
    (S : Submodule (q.Extension 2) (Fin (s + 4) → q.Extension 2))
    (hS : ∀ x ∈ S, ∀ y ∈ S, unitaryNaturalPair q (s + 3) x y = 0)
    (hd : Module.finrank (q.Extension 2) S = 2) :
    MaximalIsotropic (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) (s + 3) : Mat (q.Extension 2) (s + 3)) S := by
  apply unitary_isotropic_maximal_of_finrank q (s + 3) S hS
  exact hd.trans (by omega)

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
