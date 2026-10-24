import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalMiddleWeylScalarWord
import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalMiddleWeylCoset
import SymmetricSubgroupAsymptotics.CFSGFFourE6NormMatrixDiagonal
import SymmetricSubgroupAsymptotics.CFSGFFourE6MiddleWeylCoordinateSteps

/-! The actual source residual of a retained negative-middle scalar lies
in the actual diagonal preimage. Only one element membership is reflected
through the central quotient; no quotient automorphism is lifted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Matrix
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleScalarResidual
open CFSGReeFFourFieldParameters CFSGReeFFourFixedModelEquivalence CFSGReeFFourPerfectProjection
open CFSGReeFFourOriginalMiddleWeylScalarWord CFSGReeFFourOriginalMiddleWeylCoset
open CFSGReeFFourOriginalDiagonalNormalizer CFSGReeFFourOriginalPairDiagonal
open CFSGReeFFourOriginalNegativeMiddleRestriction CFSGReeFFourOriginalNegativeMiddleCoordinates
open CFSGReeFFourOriginalPairRestriction CFSGReeFFourOriginalPositiveNormalization
open CFSGReeFFourOppositeGenerationAssembly CFSGReeFFourFixedBruhatCover
open CFSGFFourOriginalFoldedEquivalence CFSGFFourOriginalMiddleWords CFSGFFourOriginalBruhatCells
open CFSGFFourE6NormMatrixDiagonal CFSGFFourE6MiddleWeylCoordinateSteps
open CFSGFFourE6MiddleWeylBasisLabels CFSGTwistedE6GeckNormalizerEnvelope
open CFSGFFourSerreMatrices

private theorem map_residual {G H : Type*} [Group G] [Group H] (F : G→*H)
    (x w : G) (y d : H) (hx : F x=y) (hy : y=d*F w) : F (x*w⁻¹)=d := by
  rw [map_mul,map_inv,hx,hy]
  group

def middleScalarResidual (m : ℕ) (c : Field m) : originalModelFixed m :=
  scaledMiddleWeylWord m c*(fixedMiddleWeyl m)⁻¹

theorem middleScalarResidual_mem_diagonal (m : ℕ) (hm : 0<m) (f : pairStabilizer m hm)
    (tau : Field m ≃+* Field m) (hfields : positiveLayerDescription m hm f tau tau)
    (c : Field m)
    (hc : negativeMiddleAction m hm f (CFSGSuzukiUnipotent.coordinateElement m 1 0)=
      CFSGSuzukiUnipotent.coordinateElement m c 0) :
    middleScalarResidual m c∈fixedDiagonal m := by
  obtain ⟨d,hd⟩ := pair_image_middleWeyl_mem_diagonal_coset m hm f
  have he := map_residual (fixedToOriginal m hm) (scaledMiddleWeylWord m c) (fixedMiddleWeyl m)
    (f.val (originalMiddleWeyl m hm)) d.val
    (pair_image_middle_weyl_scaled_word m hm f tau hfields c hc).symm hd
  have hpre : middleScalarResidual m c∈(originalDiagonal m hm).comap (fixedToOriginal m hm) := by
    change fixedToOriginal m hm (scaledMiddleWeylWord m c*(fixedMiddleWeyl m)⁻¹)∈originalDiagonal m hm
    rw [he]
    exact d.property
  rwa [originalDiagonal_comap] at hpre

theorem middleScalarResidual_matrix_entry_zero (m : ℕ) (hm : 0<m) (f : pairStabilizer m hm)
    (tau : Field m ≃+* Field m) (hfields : positiveLayerDescription m hm f tau tau)
    (c : Field m)
    (hc : negativeMiddleAction m hm f (CFSGSuzukiUnipotent.coordinateElement m 1 0)=
      CFSGSuzukiUnipotent.coordinateElement m c 0) :
    matrixAction (Field m)
      (modelEquivFolded (Field m) (middleScalarResidual m c).val) 13 0=0 := by
  have hD : (middleScalarResidual m c).val∈modelDiagonalPart (Field m) :=
    middleScalarResidual_mem_diagonal m hm f tau hfields c hc
  have hdiag := diagonalNormalizer_isDiag (Field m)
    (rawHom (Field m) (middleScalarResidual m c).val) hD
  exact normMatrixAction_off_diagonal_eq_zero (Field m)
    (modelEquivFolded (Field m) (middleScalarResidual m c).val) hdiag (basisIndex 13) (basisIndex 0)
    (fun he=>(by decide : (13 : Fin 26)≠0) (basisIndex_bijective.1 he))

end SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleScalarResidual
