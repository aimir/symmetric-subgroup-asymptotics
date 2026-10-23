import SymmetricSubgroupAsymptotics.CFSGHermitianGlobalFieldCoherence
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitarySemilinearPieces

/-! Higher-Witt-rank original unitary automorphisms have a single field
component on ALL maximal singular spaces. Actual normalization supplies
their dimensions, and the proved gallery propagates the common-plane
uniqueness. Gluing the vector representatives globally remains separate. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists CFSGHermitianOrthogonalSpan

theorem unitary_maximalIsotropic_finrank (q : CFSG.PrimePower) (r : ℕ)
    (S : Submodule (q.Extension 2) (Fin (r + 1) → q.Extension 2))
    (hS : MaximalIsotropic (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r) S) :
    Module.finrank (q.Extension 2) S = (r + 1) / 2 := by
  obtain ⟨g, hg⟩ := exists_unitary_maximal_subspace_normalization q r S hS
  rw [← unitarySubspaceImage_finrank q r g S, hg, unitaryStandardSingularSpace_finrank]

theorem unitary_exists_common_maximal_field_component (q : CFSG.PrimePower) (s : ℕ)
    (f : MulAut (CFSG.Models.TwistedA (s + 5) q)) :
    ∃ tau : q.Extension 2 ≃+* q.Extension 2,
      ∀ S : MaximalSpace (definingFieldAutomorphism q 2)
        (signedReversalUnit (q.Extension 2) (s + 5) : Mat (q.Extension 2) (s + 5)),
        Nonempty (SemilinearPiece (definingFieldAutomorphism q 2)
          (signedReversalUnit (q.Extension 2) (s + 5) : Mat (q.Extension 2) (s + 5))
          (unitaryOrthogonalityActionHom q (s + 2) f).val ⟨S.val, S.property.1⟩ tau) := by
  classical
  let sig := definingFieldAutomorphism q 2
  let H : Mat (q.Extension 2) (s + 5) := signedReversalUnit (q.Extension 2) (s + 5)
  let p := (unitaryOrthogonalityActionHom q (s + 2) f).val
  have hmin (S : MaximalSpace sig H) : 3 ≤ Module.finrank (q.Extension 2) S.val := by
    rw [unitary_maximalIsotropic_finrank q (s + 5) S.val S.property]
    omega
  have hpieces (S : MaximalSpace sig H) :
      ∃ tau : q.Extension 2 ≃+* q.Extension 2,
        Nonempty (SemilinearPiece sig H p ⟨S.val, S.property.1⟩ tau) := by
    apply unitary_exists_semilinearPiece q (s + 2) f _ (Module.finrank (q.Extension 2) S.val - 3)
    have hn := hmin S
    change Module.finrank (q.Extension 2) S.val = _
    omega
  choose tau htau using hpieces
  let F := fun S : MaximalSpace sig H => Classical.choice (htau S)
  let E : MaximalSpace sig H :=
    ⟨unitaryStandardSingularSpace q (s + 5), unitaryStandardSingularSpace_maximal q (s + 5)⟩
  refine ⟨tau E, fun S => ?_⟩
  have hswap (x y : Fin (s + 6) → q.Extension 2) :
      CFSGTwistedAUnitaryParameters.hermitianPair sig H x y = 0 ↔
        CFSGTwistedAUnitaryParameters.hermitianPair sig H y x = 0 :=
    unitaryNaturalPair_zero_swap q (s + 5) x y
  have he : tau S = tau E := maximal_semilinear_field_component_unique sig H p hswap hmin tau F S E
  rw [← he]
  exact htau S

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
