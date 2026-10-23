import SymmetricSubgroupAsymptotics.CFSGQuadraticHyperbolicPairStabilizer
import SymmetricSubgroupAsymptotics.CFSGTwistedDOpposedTail
import SymmetricSubgroupAsymptotics.CFSGTwistedDFixedPolePolar

/-! Arbitrary fixed-field linear isometries fixing the literal first
pair restrict to actual isometries of the SAME smaller fixed space.
No extension-field matrix lift or ambient-component recognition is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDFixedPairTailIsometry
open CFSGTwistedDFixedQuadraticSpace CFSGTwistedDFixedTailLinear
open CFSGTwistedDFixedPolePolar CFSGTwistedDOpposedTail
open CFSGTwistedDSingularDimensionBound CFSGTwistedDAllRankFixedPairFrame CFSGTwistedA2FixedField

theorem exists_tail (n : ℕ) (q : CFSG.PrimePower)
    (L : fixedSpace (n + 1) q ≃ₗ[fixedField q] fixedSpace (n + 1) q)
    (hQ : ∀ v, fixedQuadraticForm (n + 1) q (L v) = fixedQuadraticForm (n + 1) q v)
    (he : L (firstAxis (n + 1) q) = firstAxis (n + 1) q)
    (hf : L (negativeFirst (n + 1) q) = negativeFirst (n + 1) q) :
    ∃ T : fixedSpace n q ≃ₗ[fixedField q] fixedSpace n q,
      (∀ z, fixedQuadraticForm n q (T z) = fixedQuadraticForm n q z) ∧
      ∀ v, poleEquiv n q (L v) =
        (positiveHead n q v, (T (tailLinear n q v), negativeHead n q v)) := by
  let E := poleEquiv n q
  let Q := (fixedQuadraticForm (n + 1) q).comp E.symm.toLinearMap
  let M := E.symm.trans (L.trans E)
  have hform (a z b) : Q (a, (z, b)) = a * b + fixedQuadraticForm n q z :=
    quadratic_inv n q a b z
  have hM (x) : Q (M x) = Q x := by
    change fixedQuadraticForm (n + 1) q (E.symm (E (L (E.symm x)))) =
      fixedQuadraticForm (n + 1) q (E.symm x)
    rw [E.symm_apply_apply, hQ]
  have he0 : E.symm (1, (0, 0)) = firstAxis (n + 1) q := by
    apply E.injective
    rw [E.apply_symm_apply, pole_firstAxis]
  have hf0 : E.symm (0, (0, 1)) = negativeFirst (n + 1) q := by
    apply E.injective
    rw [E.apply_symm_apply, pole_negativeFirst]
  have hMe : M (1, (0, 0)) = (1, (0, 0)) := by
    change E (L (E.symm (1, (0, 0)))) = _
    rw [he0, he, pole_firstAxis]
  have hMf : M (0, (0, 1)) = (0, (0, 1)) := by
    change E (L (E.symm (0, (0, 1)))) = _
    rw [hf0, hf, pole_negativeFirst]
  obtain ⟨T, hT, hMT⟩ := CFSGQuadraticHyperbolicPairStabilizer.exists_tail
    Q (fixedQuadraticForm n q) hform M hM hMe hMf
  refine ⟨T, hT, ?_⟩
  intro v
  have h := hMT (E v).1 (E v).2.1 (E v).2.2
  change E (L (E.symm (E v))) =
    (positiveHead n q v, (T (tailLinear n q v), negativeHead n q v)) at h
  rw [E.symm_apply_apply] at h
  exact h

end SymmetricSubgroupAsymptotics.CFSGTwistedDFixedPairTailIsometry
