import SymmetricSubgroupAsymptotics.CFSGQuadraticHyperbolicPairStabilizer
import SymmetricSubgroupAsymptotics.CFSGTwistedDBasePoleCoordinates

/-! At natural rank two, stabilizing the literal first pair leaves an
actual linear isometry of the anisotropic norm plane, with both possible
components retained. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDBasePairTailIsometry
open CFSGTwistedDFixedQuadraticSpace CFSGTwistedDBasePoleCoordinates
open CFSGTwistedDAnisotropicNormForm CFSGTwistedDSingularDimensionBound
open CFSGTwistedDAllRankFixedPairFrame CFSGTwistedA2FixedField

theorem exists_tail (q : CFSG.PrimePower)
    (L : fixedSpace 0 q ≃ₗ[fixedField q] fixedSpace 0 q)
    (hQ : ∀ v, fixedQuadraticForm 0 q (L v) = fixedQuadraticForm 0 q v)
    (he : L (firstAxis 0 q) = firstAxis 0 q)
    (hf : L (negativeFirst 0 q) = negativeFirst 0 q) :
    ∃ T : q.Extension 2 ≃ₗ[fixedField q] q.Extension 2,
      (∀ z, normForm q (T z) = normForm q z) ∧
      ∀ v, basePoleEquiv q (L v) =
        ((basePoleEquiv q v).1, (T (basePoleEquiv q v).2.1, (basePoleEquiv q v).2.2)) := by
  let E := basePoleEquiv q
  let Q := (fixedQuadraticForm 0 q).comp E.symm.toLinearMap
  let M := E.symm.trans (L.trans E)
  have hform (a z b) : Q (a, (z, b)) = a * b + normForm q z := quadratic_inv q a b z
  have hM (x) : Q (M x) = Q x := by
    change fixedQuadraticForm 0 q (E.symm (E (L (E.symm x)))) = fixedQuadraticForm 0 q (E.symm x)
    rw [E.symm_apply_apply, hQ]
  have he0 : E.symm (1, (0, 0)) = firstAxis 0 q := by
    apply E.injective
    rw [E.apply_symm_apply, basePole_firstAxis]
  have hf0 : E.symm (0, (0, 1)) = negativeFirst 0 q := by
    apply E.injective
    rw [E.apply_symm_apply, basePole_negativeFirst]
  have hMe : M (1, (0, 0)) = (1, (0, 0)) := by
    change E (L (E.symm (1, (0, 0)))) = _
    rw [he0, he, basePole_firstAxis]
  have hMf : M (0, (0, 1)) = (0, (0, 1)) := by
    change E (L (E.symm (0, (0, 1)))) = _
    rw [hf0, hf, basePole_negativeFirst]
  obtain ⟨T, hT, hMT⟩ := CFSGQuadraticHyperbolicPairStabilizer.exists_tail
    Q (normForm q) hform M hM hMe hMf
  refine ⟨T, hT, ?_⟩
  intro v
  have h := hMT (E v).1 (E v).2.1 (E v).2.2
  change E (L (E.symm (E v))) = ((E v).1, (T (E v).2.1, (E v).2.2)) at h
  rw [E.symm_apply_apply] at h
  exact h

end SymmetricSubgroupAsymptotics.CFSGTwistedDBasePairTailIsometry
