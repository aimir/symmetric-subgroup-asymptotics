import SymmetricSubgroupAsymptotics.CFSGHermitianFieldNormalization
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryGlobalFieldComponent
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryLowRankGlobalField

/-! Removing the actual common field component uniformly on every
original unitary model of rank at least three. The defining Frobenius
commutes with EVERY field automorphism; the same signed form matrix is
fixed. Thus all normalized maximal-space pieces are genuinely linear. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists CFSGHermitianOrthogonalSpan

 theorem unitary_definingField_commute (q : CFSG.PrimePower)
    (tau : q.Extension 2 ≃+* q.Extension 2) :
    Function.Commute (definingFieldAutomorphism q 2) tau := by
  intro x
  change (tau x) ^ q.order = tau (x ^ q.order)
  exact (map_pow tau x q.order).symm

def unitaryFieldPointEquiv (q : CFSG.PrimePower) (r : ℕ)
    (tau : q.Extension 2 ≃+* q.Extension 2) :
    Equiv.Perm (SingularPoint (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r)) :=
  CFSGHermitianFieldAction.pointEquiv (definingFieldAutomorphism q 2) tau
    (signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r)
    (unitary_definingField_commute q tau) (map_signedReversalUnit_val tau.toRingHom r)

theorem unitary_exists_common_field_component (q : CFSG.PrimePower) (s : ℕ)
    (f : MulAut (CFSG.Models.TwistedA (s + 3) q)) :
    ∃ tau : q.Extension 2 ≃+* q.Extension 2,
      ∀ M : MaximalSpace (definingFieldAutomorphism q 2)
        (signedReversalUnit (q.Extension 2) (s + 3) : Mat (q.Extension 2) (s + 3)),
      Nonempty (SemilinearPiece (definingFieldAutomorphism q 2)
        (signedReversalUnit (q.Extension 2) (s + 3) : Mat (q.Extension 2) (s + 3))
        (unitaryOrthogonalityActionHom q s f).val ⟨M.val,M.property.1⟩ tau) := by
  by_cases hs : s ≤ 1
  · obtain ⟨tau,_,htau⟩ := unitary_lowRank_exists_common_maximal_field_component q s hs f
    exact ⟨tau,htau⟩
  · obtain ⟨n,rfl⟩ : ∃ n : ℕ, s = n + 2 := ⟨s - 2,by omega⟩
    exact unitary_exists_common_maximal_field_component q n f

theorem unitary_exists_field_normalized_linear_pieces (q : CFSG.PrimePower) (s : ℕ)
    (f : MulAut (CFSG.Models.TwistedA (s + 3) q)) :
    ∃ tau : q.Extension 2 ≃+* q.Extension 2,
      ∀ M : MaximalSpace (definingFieldAutomorphism q 2)
        (signedReversalUnit (q.Extension 2) (s + 3) : Mat (q.Extension 2) (s + 3)),
      Nonempty (SemilinearPiece (definingFieldAutomorphism q 2)
        (signedReversalUnit (q.Extension 2) (s + 3) : Mat (q.Extension 2) (s + 3))
        ((unitaryOrthogonalityActionHom q s f).val.trans (unitaryFieldPointEquiv q (s + 3) tau).symm)
        ⟨M.val,M.property.1⟩ (RingEquiv.refl (q.Extension 2))) := by
  obtain ⟨tau,htau⟩ := unitary_exists_common_field_component q s f
  refine ⟨tau,fun M => ?_⟩
  obtain ⟨F⟩ := htau M
  exact ⟨CFSGHermitianFieldAction.normalizedPiece _ tau _
    (unitaryOrthogonalityActionHom q s f).val ⟨M.val,M.property.1⟩
    (unitary_definingField_commute q tau)
    (map_signedReversalUnit_val tau.toRingHom (s + 3)) F⟩

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
