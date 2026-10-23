import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCommonOpposite
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryOpposedLocalFields
import SymmetricSubgroupAsymptotics.CFSGHermitianMaximalCrossPairing

/-! A single quadratic-field component works on every actual maximal
singular plane in natural dimensions four and five, over every field.
The original root-word common-opposite construction compares adjacent
planes, and the proved maximal-isotropic gallery propagates equality.
This is field coherence, not yet a global ambient vector extension. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists CFSGHermitianOrthogonalSpan

theorem unitary_lowRank_exists_common_maximal_field_component
    (q : CFSG.PrimePower) (s : ℕ) (hs : s ≤ 1)
    (f : MulAut (CFSG.Models.TwistedA (s + 3) q)) :
    ∃ tau : q.Extension 2 ≃+* q.Extension 2,
      Function.Commute (definingFieldAutomorphism q 2) tau ∧
      ∀ S : MaximalSpace (definingFieldAutomorphism q 2)
        (signedReversalUnit (q.Extension 2) (s + 3) : Mat (q.Extension 2) (s + 3)),
        Nonempty (unitaryLocalSemilinearPiece q s f ⟨S.val, S.property.1⟩ tau) := by
  classical
  let sig := definingFieldAutomorphism q 2
  let H : Mat (q.Extension 2) (s + 3) := signedReversalUnit (q.Extension 2) (s + 3)
  let p := (unitaryOrthogonalityActionHom q s f).val
  have hpieces (S : MaximalSpace sig H) :
      ∃ tau : q.Extension 2 ≃+* q.Extension 2,
        Function.Commute sig tau ∧
        Nonempty (SemilinearPiece sig H p ⟨S.val, S.property.1⟩ tau) :=
    exists_unitary_lowRank_semilinearPiece q s hs f S
  choose tau hcomm htau using hpieces
  let F := fun S : MaximalSpace sig H => Classical.choice (htau S)
  have hswap (x y : Fin (s + 4) → q.Extension 2) :
      CFSGTwistedAUnitaryParameters.hermitianPair sig H x y = 0 ↔
        CFSGTwistedAUnitaryParameters.hermitianPair sig H y x = 0 :=
    unitaryNaturalPair_zero_swap q (s + 3) x y
  have hstep (A B : MaximalSpace sig H) (hAB : GalleryStep sig H A B) : tau A = tau B := by
    obtain ⟨R, hAR, hBR⟩ := unitary_gallery_common_opposite q s hs A B hAB
    have hdA := unitary_maximal_plane_finrank_two q s hs A.val A.property
    have hdB := unitary_maximal_plane_finrank_two q s hs B.val B.property
    have hdR := unitary_maximal_plane_finrank_two q s hs R.val R.property
    have heA : tau A = tau R := semilinearPiece_fields_eq_of_disjoint_maximal_planes
      sig H hswap p (unitaryOrthogonalityActionHom q s f).property
      A.val R.val A.property R.property hAR hdA hdR (tau A) (tau R) (F A) (F R) (hcomm R)
    have heB : tau B = tau R := semilinearPiece_fields_eq_of_disjoint_maximal_planes
      sig H hswap p (unitaryOrthogonalityActionHom q s f).property
      B.val R.val B.property R.property hBR hdB hdR (tau B) (tau R) (F B) (F R) (hcomm R)
    exact heA.trans heB.symm
  have hsame (A B : MaximalSpace sig H) : tau A = tau B := by
    have hpath := maximal_gallery_connected sig H hswap A B
    induction hpath with
    | refl => rfl
    | @tail C D _ hCD ih => exact ih.trans (hstep C D hCD)
  let E : MaximalSpace sig H := unitaryStandardMaximalSpace q (s + 3)
  refine ⟨tau E, hcomm E, fun S => ?_⟩
  have he := hsame S E
  rw [← he]
  exact htau S

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
