import SymmetricSubgroupAsymptotics.CFSGTwistedDFixedPoleShearRelative
import SymmetricSubgroupAsymptotics.QuadraticSingularSpanPairing
import SymmetricSubgroupAsymptotics.QuadraticHyperbolicRadicalClearing
import SymmetricSubgroupAsymptotics.CFSGSplitQuadraticBasisParameters

/-! Actual all-norm vector normalization in every twisted-D natural
rank at least three. A singular vector is scaled to pairing one BEFORE
the actual relative word acts. The whole anisotropic tail is then
cleared by an actual full pole radical, in every characteristic. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedDAllNormVectorOrbit

open CFSGTwistedDFixedQuadraticSpace CFSGTwistedDFixedQuadraticAction
open CFSGTwistedDFixedQuadraticNondegenerate CFSGTwistedDRelativeElementaryGroup
open CFSGTwistedDFixedTailLinear CFSGTwistedDFixedPolePolar
open CFSGTwistedDFixedPoleShear CFSGTwistedDFixedPoleShearRelative
open CFSGTwistedDSingularDimensionBound CFSGTwistedA2FixedField
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexBundledQuadratic
open CFSGOrthogonalDIndexPrefixPerpendicular CFSGQuadraticHyperbolicShear

private theorem firstAxis_singular (n : ℕ) (q : CFSG.PrimePower) :
    fixedQuadraticForm n q (firstAxis n q) = 0 := by
  apply Subtype.ext
  rw [fixedQuadraticForm_apply]
  exact CFSGSplitQuadraticBasisParameters.positive_norm (q.Extension 2) (0 : Fin (n + 2)) 1

private theorem firstAxis_polar_head (n : ℕ) (q : CFSG.PrimePower)
    (v : fixedSpace (n + 1) q) :
    (fixedQuadraticForm (n + 1) q).polarBilin (firstAxis (n + 1) q) v =
      negativeHead n q v := by
  apply Subtype.ext
  rw [fixedQuadraticForm_polar, splitQuadraticForm_polar]
  exact polar_positive_basis (q.Extension 2) (n + 3) 0 v.val

def normRepresentative (n : ℕ) (q : CFSG.PrimePower) (c : fixedField q) :
    fixedSpace (n + 1) q := (poleEquiv n q).symm (c, (0, 1))

theorem poleShear_clear_tail (n : ℕ) (q : CFSG.PrimePower)
    (v : fixedSpace (n + 1) q) (hv : negativeHead n q v = 1) :
    poleShear n q (-tailLinear n q v) v =
      normRepresentative n q (fixedQuadraticForm (n + 1) q v) := by
  apply (poleEquiv n q).injective
  rw [poleEquiv_poleShear]
  change transform (fixedQuadraticForm n q) (-(poleEquiv n q v).2.1) (poleEquiv n q v) =
    poleEquiv n q ((poleEquiv n q).symm (fixedQuadraticForm (n + 1) q v, (0, 1)))
  rw [LinearEquiv.apply_symm_apply,
    QuadraticHyperbolicRadicalClearing.transform_clear_tail _ _ hv]
  have hQ : norm (fixedQuadraticForm n q) (poleEquiv n q v) =
      fixedQuadraticForm (n + 1) q v := (quadratic_coordinates n q v).symm
  rw [hQ]

theorem exists_normalize_norm (n : ℕ) (q : CFSG.PrimePower)
    (v : fixedSpace (n + 1) q) (hv : v ≠ 0) :
    ∃ g : relativeRootGroup (n + 1) q, fixedLinearHom (n + 1) q g v =
      normRepresentative n q (fixedQuadraticForm (n + 1) q v) := by
  obtain ⟨e, he0, heQ, he⟩ := QuadraticSingularSpanPairing.exists_singular_pairing_one
    (fixedQuadraticForm (n + 1) q) (fixedQuadraticForm_nondegenerate (n + 1) q)
    (CFSGTwistedDAllRankSingularSpanning.singular_span_eq_top (n + 1) q) v hv
  obtain ⟨a, ha⟩ := exists_fixed_map_of_singular (n + 1) q e (firstAxis (n + 1) q)
    he0 (firstAxis_nonzero (n + 1) q) heQ (firstAxis_singular (n + 1) q)
  let w := fixedLinearHom (n + 1) q a v
  have hw : negativeHead n q w = 1 := by
    have hB := QuadraticHyperbolicRadicalHom.polar_preserved
      (fixedQuadraticForm (n + 1) q) (fixedLinearHom (n + 1) q a)
      (fixedLinearHom_preserves_Q (n + 1) q a) e v
    change (fixedQuadraticForm (n + 1) q).polarBilin
        (fixedLinearHom (n + 1) q a e) (fixedLinearHom (n + 1) q a v) =
      (fixedQuadraticForm (n + 1) q).polarBilin e v at hB
    rw [ha, firstAxis_polar_head] at hB
    exact hB.trans he
  obtain ⟨b, hb⟩ := poleShear_has_element n q (-tailLinear n q w)
  refine ⟨b * a, ?_⟩
  rw [map_mul]
  change fixedLinearHom (n + 1) q b w = _
  rw [hb, poleShear_clear_tail n q w hw]
  have hQ : fixedQuadraticForm (n + 1) q w = fixedQuadraticForm (n + 1) q v :=
    fixedLinearHom_preserves_Q (n + 1) q a v
  rw [hQ]

theorem exists_map_of_same_norm (n : ℕ) (q : CFSG.PrimePower)
    (v w : fixedSpace (n + 1) q) (hv : v ≠ 0) (hw : w ≠ 0)
    (hQ : fixedQuadraticForm (n + 1) q v = fixedQuadraticForm (n + 1) q w) :
    ∃ g : relativeRootGroup (n + 1) q, fixedLinearHom (n + 1) q g v = w := by
  obtain ⟨a, ha⟩ := exists_normalize_norm n q v hv
  obtain ⟨b, hb⟩ := exists_normalize_norm n q w hw
  refine ⟨b⁻¹ * a, ?_⟩
  rw [map_mul, map_inv]
  change (fixedLinearHom (n + 1) q b).symm (fixedLinearHom (n + 1) q a v) = w
  rw [ha, hQ, ← hb, LinearEquiv.symm_apply_apply]

end SymmetricSubgroupAsymptotics.CFSGTwistedDAllNormVectorOrbit
