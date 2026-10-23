import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryOddMiddleDetermination
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryOpposedNormalization

/-! The uniform normalized odd-dimensional point action is a
CONSTRUCTED norm-one middle isometry. Fixedness of the whole singular
half-section is derived; neither that fixedness nor a middle action is
supplied as an extra input. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists CFSGHermitianOrthogonalSpan
open CFSGHermitianSimilitudeGroup

def unitaryOddMiddleSimilitude (q : CFSG.PrimePower) (m : ℕ) (c : q.Extension 2)
    (hc : c ≠ 0) (hcn : definingFieldAutomorphism q 2 c * c = 1) :
    similitudes (definingFieldAutomorphism q 2) (signedReversalUnit (q.Extension 2) (2*m+4)) :=
  ⟨unitaryOddMiddleScaleEquiv q m c hc,1,one_ne_zero,by
    intro x y
    change unitaryNaturalPair q (2*m+4) (unitaryOddMiddleScale q m c x) (unitaryOddMiddleScale q m c y) =
      1 * unitaryNaturalPair q (2*m+4) x y
    rw [one_mul]
    exact unitaryOddMiddleScale_pair q m c hcn x y⟩

theorem exists_unitary_odd_normalized_point_realization (q : CFSG.PrimePower) (m : ℕ)
    (f : Equiv.Perm (UnitaryOddPoint q m))
    (hf : PreservesOrthogonality (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) (2*m+4) : Mat (q.Extension 2) (2*m+4)) f)
    (hlinear : UnitaryLinearPointPieces q (2*m+4) f)
    (hfixP : ∀ R : UnitaryOddPoint q m, R.val ≤ unitaryStandardSingularSpace q (2*m+4) → f R = R)
    (hfixZ : ∀ R : UnitaryOddPoint q m, R.val ≤ unitaryOppositeSingularSpace q (2*m+4) → f R = R)
    (hfixMixed : ∀ (x y : Fin (2*m+5) → q.Extension 2),
      x ∈ unitaryStandardSingularSpace q (2*m+4) → x ≠ 0 →
      y ∈ unitaryOppositeSingularSpace q (2*m+4) → y ≠ 0 → unitaryNaturalPair q (2*m+4) y x = 0 →
      ∀ R : UnitaryOddPoint q m, R.val = (q.Extension 2) ∙ (x+y) → f R = R) :
    ∃ g : similitudes (definingFieldAutomorphism q 2) (signedReversalUnit (q.Extension 2) (2*m+4)),
      ∀ R : UnitaryOddPoint q m, f R = singularPointHom (definingFieldAutomorphism q 2)
        (signedReversalUnit (q.Extension 2) (2*m+4)) g R := by
  have hW : ∀ R : UnitaryOddPoint q m, R.val ≤ unitaryOddHalf q m → f R = R :=
    unitary_odd_half_pointwise_fix_of_mixed q (2*m+1) ⟨m+2,by omega⟩ f hlinear hfixP hfixZ hfixMixed
  obtain ⟨c,hc,hcn,hpoints⟩ := unitaryOdd_point_action_middle_scale q m f hf hlinear hfixP hfixZ hfixMixed hW
  let g := unitaryOddMiddleSimilitude q m c hc hcn
  refine ⟨g,?_⟩
  intro R
  apply Subtype.ext
  exact (hpoints R).trans
    (singularPointHom_val (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) (2*m+4)) g R).symm

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
