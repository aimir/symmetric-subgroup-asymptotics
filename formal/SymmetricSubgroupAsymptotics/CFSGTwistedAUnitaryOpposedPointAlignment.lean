import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryOpposedIsometryExtension
import SymmetricSubgroupAsymptotics.CFSGHermitianPiecePointCompatibility

/-! A literal unitary point permutation with local linear pieces can be
aligned on BOTH original opposed coordinate halves by a constructed
ambient isometry. No transitivity on pairs of target maximal spaces or
supplied ambient realization is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists CFSGHermitianOrthogonalSpan
open CFSGHermitianSimilitudeGroup

theorem exists_unitary_opposed_point_alignment (q : CFSG.PrimePower) (r : ℕ) (hr : 3 ≤ r)
    (f : Equiv.Perm (SingularPoint (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r)))
    (hf : PreservesOrthogonality (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r) f)
    (hlinear : ∀ M : MaximalSpace (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r),
      Nonempty (SemilinearPiece (definingFieldAutomorphism q 2)
        (signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r) f
        ⟨M.val,M.property.1⟩ (RingEquiv.refl (q.Extension 2)))) :
    ∃ g : similitudes (definingFieldAutomorphism q 2) (signedReversalUnit (q.Extension 2) r),
      (∀ R : SingularPoint (definingFieldAutomorphism q 2)
        (signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r),
        R.val ≤ unitaryStandardSingularSpace q r →
          singularPointHom (definingFieldAutomorphism q 2) (signedReversalUnit (q.Extension 2) r) g R = f R) ∧
      ∀ R : SingularPoint (definingFieldAutomorphism q 2)
        (signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r),
        R.val ≤ unitaryOppositeSingularSpace q r →
          singularPointHom (definingFieldAutomorphism q 2) (signedReversalUnit (q.Extension 2) r) g R = f R := by
  obtain ⟨F⟩ := hlinear (unitaryStandardMaximalSpace q r)
  obtain ⟨G⟩ := hlinear (unitaryOppositeMaximalSpace q r)
  obtain ⟨c,hc,e,he,hP,hZ⟩ := exists_unitary_opposed_isometry_extension q r hr f hf F G
  let g : similitudes (definingFieldAutomorphism q 2) (signedReversalUnit (q.Extension 2) r) :=
    ⟨e,1,one_ne_zero,fun x y => (he x y).trans (one_mul _).symm⟩
  refine ⟨g,?_,?_⟩
  · intro R hR
    exact singularPointHom_eq_of_piece_scalar (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) r) f (unitaryStandardIsotropicSpace q r) F g 1 one_ne_zero
      (fun x => (hP x).trans (one_smul _ _).symm) R hR
  · intro R hR
    exact singularPointHom_eq_of_piece_scalar (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) r) f (unitaryOppositeIsotropicSpace q r) G g c⁻¹
      (inv_ne_zero hc) hZ R hR

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
