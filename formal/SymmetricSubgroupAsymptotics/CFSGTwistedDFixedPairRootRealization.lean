import SymmetricSubgroupAsymptotics.CFSGTwistedDRootPlaneImage

/-! A totally singular independent ordered pair in the actual fixed
space realizes its literal fixed-field skew pair operator by an actual
relative root word. The checked relative pair frame fixes both vectors
exactly, so no extension-field conjugator or coefficient is introduced. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDFixedPairRootRealization
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexBundledQuadratic
open CFSGTwistedDRelativeElementaryGroup CFSGTwistedDFixedQuadraticSpace
open CFSGTwistedDFixedQuadraticAction CFSGTwistedDHighestPairOperator
open CFSGTwistedDPlaneRootLine CFSGTwistedDRootPlaneImage
open CFSGTwistedDSingularPlaneOrbit CFSGTwistedA2FixedField
open CFSGAlternatingPairOperator

theorem exists_fixed_pair_frame (s : ℕ) (q : CFSG.PrimePower)
    (v w : fixedSpace (s + 2) q) (hv : v ≠ 0)
    (hQv : fixedQuadraticForm (s + 2) q v = 0)
    (hQw : fixedQuadraticForm (s + 2) q w = 0)
    (hvw : (fixedQuadraticForm (s + 2) q).polarBilin v w = 0)
    (hnot : ∀ c : fixedField q, w ≠ c • v) :
    ∃ g : relativeRootGroup (s + 2) q,
      fixedLinearHom (s + 2) q g v = firstVector s q ∧
      fixedLinearHom (s + 2) q g w = secondVector s q := by
  have hvK := congrArg (fun a : fixedField q => (a : q.Extension 2)) hQv
  have hwK := congrArg (fun a : fixedField q => (a : q.Extension 2)) hQw
  have hpK := congrArg (fun a : fixedField q => (a : q.Extension 2)) hvw
  dsimp only at hvK hwK hpK
  rw [fixedQuadraticForm_apply] at hvK hwK
  rw [fixedQuadraticForm_polar, splitQuadraticForm_polar] at hpK
  obtain ⟨g, hgv, hgw⟩ := CFSGTwistedDSingularPairOrbit.exists_singular_pair_frame s q
    v.val w.val v.property w.property (fun he => hv (Subtype.ext he)) hvK hwK hpK
    (fun c he => hnot c (Subtype.ext he))
  refine ⟨g, ?_, ?_⟩
  · apply Subtype.ext
    rw [fixedLinearHom_apply, firstVector_val]
    exact hgv
  · apply Subtype.ext
    rw [fixedLinearHom_apply, secondVector_val]
    exact hgw

theorem exists_root_pair_action (s : ℕ) (q : CFSG.PrimePower)
    (v w : fixedSpace (s + 2) q) (hv : v ≠ 0)
    (hQv : fixedQuadraticForm (s + 2) q v = 0)
    (hQw : fixedQuadraticForm (s + 2) q w = 0)
    (hvw : (fixedQuadraticForm (s + 2) q).polarBilin v w = 0)
    (hnot : ∀ c : fixedField q, w ≠ c • v) :
    ∃ g : relativeRootGroup (s + 2) q,
      conjugateRootPlane s q g = Submodule.span (fixedField q) {v, w} ∧
      ∀ a : fixedField q, ∀ z : fixedSpace (s + 2) q,
        fixedLinearHom (s + 2) q (g * highestRoot s q a * g⁻¹) z =
          z + a • pairOperator (fixedQuadraticForm (s + 2) q).polarBilin v w z := by
  obtain ⟨g, hgv, hgw⟩ := exists_fixed_pair_frame s q v w hv hQv hQw hvw hnot
  have h0 : fixedLinearHom (s + 2) q g⁻¹ (firstVector s q) = v := by
    have he := congrArg (fixedLinearHom (s + 2) q g).symm hgv
    rw [LinearEquiv.symm_apply_apply] at he
    simpa only [map_inv] using he.symm
  have h1 : fixedLinearHom (s + 2) q g⁻¹ (secondVector s q) = w := by
    have he := congrArg (fixedLinearHom (s + 2) q g).symm hgw
    rw [LinearEquiv.symm_apply_apply] at he
    simpa only [map_inv] using he.symm
  refine ⟨g⁻¹, ?_, ?_⟩
  · rw [conjugateRootPlane_eq_span, h0, h1]
  · intro a z
    rw [conjugate_highest_action, h0, h1]

end SymmetricSubgroupAsymptotics.CFSGTwistedDFixedPairRootRealization
