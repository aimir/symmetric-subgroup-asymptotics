import SymmetricSubgroupAsymptotics.CFSGTwistedDNormPlaneLift
import SymmetricSubgroupAsymptotics.CFSGTwistedDNormIsometryParameters
import SymmetricSubgroupAsymptotics.CFSGTwistedDResidualDiagonal

/-! The residual norm-plane parameter homomorphism is actual, and
every retained rotation is the SAME literal paired-torus root word.
This binds the parameter index to the original relative-root image. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDNormPlaneLiftWords
open CFSGTwistedDFixedQuadraticSpace CFSGTwistedDFixedQuadraticAction
open CFSGTwistedDLinearParameters CFSGTwistedDNormPlaneLift
open CFSGTwistedDRelativeElementaryGroup CFSGTwistedDResidualDiagonal
open CFSGTwistedDNormIsometryParameters CFSGTwistedDNormOneTorusIndex
open CFSGTwistedDNormOneUnits CFSGTwistedA2FixedField
open CFSGOrthogonalDCoordinateDiagonal CFSGOrthogonalDGenerationForkTorus

def liftHom (n : ℕ) (q : CFSG.PrimePower) :
    normIsometries q →* (fixedSpace n q ≃ₗ[fixedField q] fixedSpace n q) where
  toFun T := lift n q T.val
  map_one' := by
    apply LinearEquiv.ext
    intro v
    apply (linearParameters n q).injective
    rw [coordinates]
    rfl
  map_mul' T U := by
    apply LinearEquiv.ext
    intro v
    apply (linearParameters n q).injective
    change linearParameters n q (lift n q (T * U).val v) =
      linearParameters n q (lift n q T.val (lift n q U.val v))
    rw [coordinates, coordinates, coordinates]
    rfl

theorem rotation_eq_word (n : ℕ) (q : CFSG.PrimePower)
    (c : normOneUnits q) (hc : c ∈ retainedResidual q) :
    lift n q (rotationHom q c).val = fixedLinearHom n q
      ⟨residualDiagonalHom n q c, retained_residual_diagonal_mem n q c hc⟩ := by
  let g : relativeRootGroup n q :=
    ⟨residualDiagonalHom n q c, retained_residual_diagonal_mem n q c hc⟩
  apply LinearEquiv.ext
  intro v
  apply (linearParameters n q).injective
  rw [coordinates]
  apply Prod.ext
  · funext j
    apply Subtype.ext
    change v.val (Sum.inl j.castSucc) = (fixedLinearHom n q g v).val (Sum.inl j.castSucc)
    rw [fixedLinearHom_apply]
    change v.val (Sum.inl j.castSucc) =
      ((pairDiagonalHom (q.Extension 2) (n + 2) (last n) c.val : CFSGOrthogonalDSerreMatrices.Mat (q.Extension 2) (n + 2)) *ᵥ v.val) (Sum.inl j.castSucc)
    rw [pairDiagonalHom_val, Matrix.mulVec_diagonal]
    have hj : j.castSucc ≠ last n := Fin.castSucc_ne_last j
    simp only [Sum.elim_inl, if_neg hj, one_mul]
  · apply Prod.ext
    · funext j
      apply Subtype.ext
      change v.val (Sum.inr j.castSucc) = (fixedLinearHom n q g v).val (Sum.inr j.castSucc)
      rw [fixedLinearHom_apply]
      change v.val (Sum.inr j.castSucc) =
        ((pairDiagonalHom (q.Extension 2) (n + 2) (last n) c.val : CFSGOrthogonalDSerreMatrices.Mat (q.Extension 2) (n + 2)) *ᵥ v.val) (Sum.inr j.castSucc)
      rw [pairDiagonalHom_val, Matrix.mulVec_diagonal]
      have hj : j.castSucc ≠ last n := Fin.castSucc_ne_last j
      simp only [Sum.elim_inr, if_neg hj, one_mul]
    · change (c.val : q.Extension 2) * v.val (Sum.inl (last n)) =
        (fixedLinearHom n q g v).val (Sum.inl (last n))
      rw [fixedLinearHom_apply]
      change (c.val : q.Extension 2) * v.val (Sum.inl (last n)) =
        ((pairDiagonalHom (q.Extension 2) (n + 2) (last n) c.val : CFSGOrthogonalDSerreMatrices.Mat (q.Extension 2) (n + 2)) *ᵥ v.val) (Sum.inl (last n))
      rw [pairDiagonalHom_val, Matrix.mulVec_diagonal]
      simp only [Sum.elim_inl, if_true]

theorem retained_lift_mem_range (n : ℕ) (q : CFSG.PrimePower)
    (T : normIsometries q) (hT : T ∈ retainedRotations q) :
    liftHom n q T ∈ (fixedLinearHom n q).range := by
  obtain ⟨c, hc, rfl⟩ := hT
  refine ⟨⟨residualDiagonalHom n q c, retained_residual_diagonal_mem n q c hc⟩, ?_⟩
  exact (rotation_eq_word n q c hc).symm

end SymmetricSubgroupAsymptotics.CFSGTwistedDNormPlaneLiftWords
