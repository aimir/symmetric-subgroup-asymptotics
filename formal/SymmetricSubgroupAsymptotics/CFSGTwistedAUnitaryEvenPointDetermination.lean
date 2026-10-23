import SymmetricSubgroupAsymptotics.CFSGHermitianEvenFixation
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryPointCommonRatio
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryHalfDecomposition
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryOpposedLocalFields

/-! Complete normalized point determination in every EVEN original
unitary vector dimension, with no local-linearity or rank-two premise.
The two actual opposed halves and fixed strong mixed rays suffice. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists CFSGHermitianOrthogonalSpan

theorem unitary_even_point_determination (q : CFSG.PrimePower) (s : ℕ) (hr : Odd (s+3))
    (f : Equiv.Perm (UnitaryPoint q (s+3)))
    (hf : PreservesOrthogonality (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) (s+3) : Mat (q.Extension 2) (s+3)) f)
    (hfixP : ∀ R : UnitaryPoint q (s+3), R.val ≤ unitaryStandardSingularSpace q (s+3) → f R = R)
    (hfixZ : ∀ R : UnitaryPoint q (s+3), R.val ≤ unitaryOppositeSingularSpace q (s+3) → f R = R)
    (hfixMixed : ∀ (x y : Fin (s+4) → q.Extension 2),
      x ∈ unitaryStandardSingularSpace q (s+3) → x ≠ 0 →
      y ∈ unitaryOppositeSingularSpace q (s+3) → y ≠ 0 → unitaryNaturalPair q (s+3) y x = 0 →
      ∀ R : UnitaryPoint q (s+3), R.val = (q.Extension 2) ∙ (x+y) → f R = R) :
    ∀ R : UnitaryPoint q (s+3), f R = R := by
  apply hermitian_even_fixes_all (definingFieldAutomorphism q 2)
    (signedReversalUnit (q.Extension 2) (s+3) : Mat (q.Extension 2) (s+3))
    (unitaryNaturalPair_zero_swap q (s+3)) f hf
    (unitaryStandardIsotropicSpace q (s+3)) (unitaryOppositeIsotropicSpace q (s+3)) ?_
    (unitaryStandard_opposite_disjoint q (s+3))
    (unitaryStandard_opposite_sup_eq_top_of_odd q (s+3) hr)
    (unitaryStandard_pair_opposite_nondegenerate q (s+3))
    (unitaryOpposite_pair_standard_nondegenerate q (s+3)) hfixP hfixZ hfixMixed
  change 2 ≤ Module.finrank (q.Extension 2) (unitaryStandardSingularSpace q (s+3))
  rw [unitaryStandardSingularSpace_finrank]
  omega

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
