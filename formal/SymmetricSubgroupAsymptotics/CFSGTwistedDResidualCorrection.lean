import SymmetricSubgroupAsymptotics.CFSGTwistedDDoubleTailEmbedding
import SymmetricSubgroupAsymptotics.CFSGTwistedDSingularPlaneOrbit
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexResidualCorrection

/-! A fixed-field twice-tail corrected against an original companion
retains its literal tail, its quadratic form, and orthogonality to both
positive head axes. The construction applies in characteristic two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDResidualCorrection
open CFSGTwistedDFixedQuadraticSpace CFSGTwistedDDoubleTailEmbedding
open CFSGTwistedDHighestPairOperator CFSGTwistedDSingularPlaneOrbit CFSGTwistedA2FixedField
open CFSGHyperbolicTransverseCorrection CFSGOrthogonalDIndexQuadraticCorrection
open CFSGOrthogonalDIndexTailCoordinates

theorem doubleRestriction_first (s : ℕ) (q : CFSG.PrimePower) :
    doubleRestriction s q (firstVector s q) = 0 := by
  apply Subtype.ext
  change twiceTailRestriction (q.Extension 2) (s + 2)
    (CFSGOrthogonalDIndexFlagVectors.firstVector (q.Extension 2) s) = 0
  exact CFSGOrthogonalDIndexResidualCorrection.twiceTailRestriction_first (q.Extension 2) (s + 2)

theorem doubleRestriction_second (s : ℕ) (q : CFSG.PrimePower) :
    doubleRestriction s q (secondVector s q) = 0 := by
  apply Subtype.ext
  change twiceTailRestriction (q.Extension 2) (s + 2)
    (CFSGOrthogonalDIndexFlagVectors.secondVector (q.Extension 2) s) = 0
  exact CFSGOrthogonalDIndexResidualCorrection.twiceTailRestriction_second (q.Extension 2) (s + 2)

theorem axes_polar_zero (s : ℕ) (q : CFSG.PrimePower) :
    (fixedQuadraticForm (s + 2) q).polarBilin (firstVector s q) (secondVector s q) = 0 ∧
      (fixedQuadraticForm (s + 2) q).polarBilin (secondVector s q) (secondVector s q) = 0 := by
  constructor
  · rw [first_polar]
    apply Subtype.ext
    change (Pi.single (Sum.inl (CFSGOrthogonalDIndexFlagVectors.secondIndex s))
      (1 : q.Extension 2) : CFSGOrthogonalDSerreMatrices.Index (s + 4) → q.Extension 2)
        (Sum.inr 0) = 0
    simp only [Pi.single_apply, Sum.inl_ne_inr, Sum.inr_ne_inl, if_false]
  · rw [second_polar]
    apply Subtype.ext
    change (Pi.single (Sum.inl (CFSGOrthogonalDIndexFlagVectors.secondIndex s))
      (1 : q.Extension 2) : CFSGOrthogonalDSerreMatrices.Index (s + 4) → q.Extension 2)
        (Sum.inr 1) = 0
    simp only [Pi.single_apply, Sum.inl_ne_inr, Sum.inr_ne_inl, if_false]

def residualMap (s : ℕ) (q : CFSG.PrimePower) (w : fixedSpace (s + 2) q) :
    fixedSpace s q →ₗ[fixedField q] fixedSpace (s + 2) q :=
  correction (fixedQuadraticForm (s + 2) q).polarBilin
    (secondVector s q) w (doubleEmbed s q)

theorem residualMap_leftInverse (s : ℕ) (q : CFSG.PrimePower)
    (w : fixedSpace (s + 2) q) (z : fixedSpace s q) :
    doubleRestriction s q (residualMap s q w z) = z :=
  correction_leftInverse _ _ _ _ _ (doubleRestriction_doubleEmbed s q)
    (doubleRestriction_second s q) z

theorem residualMap_quadratic (s : ℕ) (q : CFSG.PrimePower)
    (w : fixedSpace (s + 2) q) (z : fixedSpace s q) :
    fixedQuadraticForm (s + 2) q (residualMap s q w z) = fixedQuadraticForm s q z := by
  have he : fixedQuadraticForm (s + 2) q (secondVector s q) = 0 :=
    standardRootPlane_singular s q _ (Submodule.subset_span (Or.inr rfl))
  have hje (t : fixedSpace s q) :
      (fixedQuadraticForm (s + 2) q).polarBilin (doubleEmbed s q t) (secondVector s q) = 0 := by
    exact (QuadraticMap.polar_comm (fixedQuadraticForm (s + 2) q : _ → fixedField q) _ _).trans
      (doubleEmbed_perp_second s q t)
  change fixedQuadraticForm (s + 2) q
    (correction (fixedQuadraticForm (s + 2) q).polarBilin
      (secondVector s q) w (doubleEmbed s q) z) = _
  rw [correction_quadratic _ _ _ _ he hje z, doubleEmbed_quadratic]

theorem residualMap_perp_companion (s : ℕ) (q : CFSG.PrimePower)
    (w : fixedSpace (s + 2) q)
    (hw : (fixedQuadraticForm (s + 2) q).polarBilin w (secondVector s q) ≠ 0)
    (z : fixedSpace s q) :
    (fixedQuadraticForm (s + 2) q).polarBilin w (residualMap s q w z) = 0 :=
  correction_orthogonal _ _ _ _ hw z

theorem residualMap_perp_first (s : ℕ) (q : CFSG.PrimePower)
    (w : fixedSpace (s + 2) q) (z : fixedSpace s q) :
    (fixedQuadraticForm (s + 2) q).polarBilin (firstVector s q) (residualMap s q w z) = 0 :=
  correction_orthogonal_to _ _ _ _ _ (axes_polar_zero s q).1 (doubleEmbed_perp_first s q) z

theorem residualMap_perp_second (s : ℕ) (q : CFSG.PrimePower)
    (w : fixedSpace (s + 2) q) (z : fixedSpace s q) :
    (fixedQuadraticForm (s + 2) q).polarBilin (secondVector s q) (residualMap s q w z) = 0 :=
  correction_orthogonal_to _ _ _ _ _ (axes_polar_zero s q).2 (doubleEmbed_perp_second s q) z

end SymmetricSubgroupAsymptotics.CFSGTwistedDResidualCorrection
