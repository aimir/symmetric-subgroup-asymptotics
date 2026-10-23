import SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankFixedPairFrame
import SymmetricSubgroupAsymptotics.CFSGSplitQuadraticBasisParameters
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPrefixPerpendicular

/-! An arbitrary actual F-linear isometry admits first-pair
normalization by ONE literal relative-root word. Ambient K-linearity is
neither assumed nor supplied as a lifting premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDFixedIsometryFirstPair
open CFSGTwistedDFixedQuadraticSpace CFSGTwistedDFixedQuadraticAction
open CFSGTwistedDSingularDimensionBound CFSGTwistedDAllRankFixedPairFrame
open CFSGTwistedDRelativeElementaryGroup CFSGTwistedA2FixedField
open CFSGOrthogonalDIndexBundledQuadratic CFSGOrthogonalDIndexPolarForm

theorem first_quadratic (n : ℕ) (q : CFSG.PrimePower) :
    fixedQuadraticForm n q (firstAxis n q) = 0 := by
  apply Subtype.ext
  rw [fixedQuadraticForm_apply]
  exact CFSGSplitQuadraticBasisParameters.positive_norm (q.Extension 2) 0 1

theorem negative_quadratic (n : ℕ) (q : CFSG.PrimePower) :
    fixedQuadraticForm n q (negativeFirst n q) = 0 := by
  apply Subtype.ext
  rw [fixedQuadraticForm_apply]
  exact CFSGSplitQuadraticBasisParameters.negative_norm (q.Extension 2) 0 1

theorem axes_polar (n : ℕ) (q : CFSG.PrimePower) :
    (fixedQuadraticForm n q).polarBilin (firstAxis n q) (negativeFirst n q) = 1 := by
  apply Subtype.ext
  rw [fixedQuadraticForm_polar, splitQuadraticForm_polar]
  change polar (q.Extension 2) (Pi.single (Sum.inl (0 : Fin (n + 2))) 1)
    (Pi.single (Sum.inr (0 : Fin (n + 2))) 1) = 1
  rw [CFSGOrthogonalDIndexPrefixPerpendicular.polar_positive_basis]
  exact Pi.single_eq_same _ _

theorem exists_normalize (n : ℕ) (q : CFSG.PrimePower)
    (L : fixedSpace n q ≃ₗ[fixedField q] fixedSpace n q)
    (hQ : ∀ v, fixedQuadraticForm n q (L v) = fixedQuadraticForm n q v) :
    ∃ g : relativeRootGroup n q,
      (L.trans (fixedLinearHom n q g)) (firstAxis n q) = firstAxis n q ∧
      (L.trans (fixedLinearHom n q g)) (negativeFirst n q) = negativeFirst n q := by
  have hB (v w : fixedSpace n q) :
      (fixedQuadraticForm n q).polarBilin (L v) (L w) =
        (fixedQuadraticForm n q).polarBilin v w := by
    change fixedQuadraticForm n q (L v + L w) - fixedQuadraticForm n q (L v) -
      fixedQuadraticForm n q (L w) =
        fixedQuadraticForm n q (v + w) - fixedQuadraticForm n q v - fixedQuadraticForm n q w
    rw [← L.map_add, hQ, hQ, hQ]
  obtain ⟨g, he, hf⟩ := exists_fixed_pair_frame n q
    (L (firstAxis n q)) (L (negativeFirst n q))
    (fun h => firstAxis_nonzero n q (L.injective (h.trans L.map_zero.symm)))
    ((hQ _).trans (first_quadratic n q)) ((hQ _).trans (negative_quadratic n q))
    ((hB _ _).trans (axes_polar n q))
  exact ⟨g, he, hf⟩

end SymmetricSubgroupAsymptotics.CFSGTwistedDFixedIsometryFirstPair
