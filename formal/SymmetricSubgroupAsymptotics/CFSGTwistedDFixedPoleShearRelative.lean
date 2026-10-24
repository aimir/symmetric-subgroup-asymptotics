import SymmetricSubgroupAsymptotics.CFSGTwistedDFixedPoleSeedAction
import SymmetricSubgroupAsymptotics.CFSGTwistedDFixedPoleTailAction
import SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankSingularSpanning
import SymmetricSubgroupAsymptotics.ScalarSpanMultiplicativeHomRange

/-! Full pole shears belong to the actual relative-root group in every
ambient natural rank at least three. Singular parameters are transported
from the literal seed by actual tail words; genuine singular spanning
then extends group-image membership to every parameter. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedDFixedPoleShearRelative

open CFSGTwistedDFixedQuadraticSpace CFSGTwistedDFixedQuadraticAction
open CFSGTwistedDRelativeElementaryGroup CFSGTwistedDRelativeTailEmbedding
open CFSGTwistedDFixedPoleShear CFSGTwistedDFixedPoleTailAction
open CFSGTwistedDFixedPoleSeedAction CFSGTwistedDAllRankPoleSeed
open CFSGTwistedDAllRankSingularOrbit CFSGTwistedDSingularDimensionBound
open CFSGTwistedA2FixedField

theorem exists_fixed_map_of_singular (n : ℕ) (q : CFSG.PrimePower)
    (v w : fixedSpace n q) (hv : v ≠ 0) (hw : w ≠ 0)
    (hQv : fixedQuadraticForm n q v = 0) (hQw : fixedQuadraticForm n q w = 0) :
    ∃ g : relativeRootGroup n q, fixedLinearHom n q g v = w := by
  have hvQ := congrArg (fun a : fixedField q => (a : q.Extension 2)) hQv
  have hwQ := congrArg (fun a : fixedField q => (a : q.Extension 2)) hQw
  dsimp only at hvQ hwQ
  rw [fixedQuadraticForm_apply] at hvQ hwQ
  obtain ⟨a, ha⟩ := exists_normalize_all n q v.val v.property hvQ
    (fun h => hv (Subtype.ext h))
  obtain ⟨b, hb⟩ := exists_normalize_all n q w.val w.property hwQ
    (fun h => hw (Subtype.ext h))
  have hfa : fixedLinearHom n q a v = firstAxis n q := by
    apply Subtype.ext
    rw [fixedLinearHom_apply]
    exact ha
  have hfb : fixedLinearHom n q b w = firstAxis n q := by
    apply Subtype.ext
    rw [fixedLinearHom_apply]
    exact hb
  refine ⟨b⁻¹ * a, ?_⟩
  rw [map_mul, map_inv]
  change (fixedLinearHom n q b).symm (fixedLinearHom n q a v) = w
  rw [hfa, ← hfb, LinearEquiv.symm_apply_apply]

theorem singular_poleShear_has_element (n : ℕ) (q : CFSG.PrimePower)
    (z : fixedSpace n q) (hz : fixedQuadraticForm n q z = 0) :
    ∃ u : relativeRootGroup (n + 1) q,
      fixedLinearHom (n + 1) q u = parameterHom n q (Multiplicative.ofAdd z) := by
  by_cases hz0 : z = 0
  · subst z
    refine ⟨1, ?_⟩
    apply LinearEquiv.ext
    intro v
    rw [map_one]
    exact (poleShear_zero_apply n q v).symm
  obtain ⟨g, hg⟩ := exists_fixed_map_of_singular n q z (seedVector n q) hz0
    (seedVector_nonzero n q) hz (seedVector_singular n q)
  let t := tailRelativeHom n q g
  refine ⟨t⁻¹ * seedElement n q * t, ?_⟩
  apply LinearEquiv.ext
  intro v
  rw [map_mul, map_mul, map_inv]
  change (fixedLinearHom (n + 1) q t).symm
    (fixedLinearHom (n + 1) q (seedElement n q) (fixedLinearHom (n + 1) q t v)) =
      poleShear n q z v
  rw [seedElement_is_poleShear]
  change (fixedLinearHom (n + 1) q t).symm
    (poleShear n q (seedVector n q) (fixedLinearHom (n + 1) q t v)) = _
  have hcov : fixedLinearHom (n + 1) q t (poleShear n q z v) =
      poleShear n q (seedVector n q) (fixedLinearHom (n + 1) q t v) := by
    simpa only [hg] using tail_poleShear_intertwine n q g z v
  rw [← hcov, LinearEquiv.symm_apply_apply]

theorem parameterHom_mem_relative_range (n : ℕ) (q : CFSG.PrimePower)
    (z : fixedSpace n q) :
    parameterHom n q (Multiplicative.ofAdd z) ∈ (fixedLinearHom (n + 1) q).range := by
  apply ScalarSpanMultiplicativeHomRange.mem_of_span_eq_top (K := fixedField q)
    (parameterHom n q) (fixedLinearHom (n + 1) q).range
      {z : fixedSpace n q | fixedQuadraticForm n q z = 0}
  · intro t ht a
    apply singular_poleShear_has_element n q
    change fixedQuadraticForm n q (a • t) = 0
    rw [QuadraticMap.map_smul, ht, smul_zero]
  · exact CFSGTwistedDAllRankSingularSpanning.singular_span_eq_top n q

theorem poleShear_has_element (n : ℕ) (q : CFSG.PrimePower)
    (z : fixedSpace n q) :
    ∃ u : relativeRootGroup (n + 1) q, ∀ v : fixedSpace (n + 1) q,
      fixedLinearHom (n + 1) q u v = poleShear n q z v := by
  obtain ⟨u, hu⟩ := parameterHom_mem_relative_range n q z
  refine ⟨u, ?_⟩
  intro v
  exact congrArg (fun A : fixedSpace (n + 1) q ≃ₗ[fixedField q] fixedSpace (n + 1) q => A v) hu

end SymmetricSubgroupAsymptotics.CFSGTwistedDFixedPoleShearRelative
