import SymmetricSubgroupAsymptotics.CFSGFFourOriginalDiagonalScalars
import SymmetricSubgroupAsymptotics.CFSGFFourOriginalProductTorus
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootLineNormalizers

/-! Actual torus realization of the retained original F4 diagonal part.
Four scalar actions are matched by the unimodular relative Cartan map;
their quotient is then killed by proved characteristic-two faithfulness. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourOriginalDiagonalTorus
open CFSG.Models.Chevalley CFSGSerreModelRootGeneration
open CFSGFFourOriginalDiagonalScalars CFSGFFourOriginalProductTorus
open CFSGFFourOriginalMiddleWords CFSGFFourOriginalBruhatCells
open CFSGFFourOriginalGeneratedEquivalence CFSGFFourRelativeScalarIndex
open CFSGIntegerMatrixPowerHom CFSGE6GeckProductTorus CFSGFFourE6ProductTorus
open CFSGTwistedE6GeckDiagramCovariance CFSGTwistedE6GeckRelativeRootGenerated
open CFSGTwistedE6GeckSourceAction CFSGTwistedE6GeckPositiveTwist
open CFSGNormTwoCoordinateRootLineNormalizers CFSGExceptionalCartanPositiveDefinite
variable (K : Type) [Field K] [Finite K] [CharP K 2]

private theorem quotient_fixes_of_same_conjugation {G : Type*} [Group G]
    (d t x : G) (he : d*x*d⁻¹=t*x*t⁻¹) :
    (t⁻¹*d)*x*(t⁻¹*d)⁻¹=x := by
  calc
    _=t⁻¹*(d*x*d⁻¹)*t := by group
    _=t⁻¹*(t*x*t⁻¹)*t := by rw [he]
    _=x := by group

theorem modelProductTorus_mem_diagonal (x : Fin 4→Kˣ) :
    modelProductTorusHom K x∈modelDiagonalPart K := by
  have ht := rawProductTorus_mem_torus K (torusTuple K x)
  have hnorm (neg : Bool) : rawHom K (modelProductTorusHom K x)∈
      Subgroup.normalizer (SignedUpper K neg : Set (Matrix GeckIndex GeckIndex K)ˣ) := by
    rw [rawHom_modelProductTorus]
    exact torusGroup_normalizes CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
      E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K neg ht
  have hM : rawHom K (modelProductTorusHom K x)∈MatrixGroup K := by
    have h := CFSGTwistedE6GeckFixedRangePreimage.fixedRootGenerated_le_matrixGroup K (RingEquiv.refl K)
      (modelEquivGenerated K (modelProductTorusHom K x)).property
    simpa only [modelEquivGenerated_val] using h
  exact ⟨⟨hnorm false,hnorm true⟩,hM⟩

theorem exists_model_diagonal_torus (d : Model CartanMatrix.F₄ K)
    (hdD : d∈modelDiagonalPart K) :
    ∃x : Fin 4→Kˣ,d=modelProductTorusHom K x := by
  obtain ⟨c,hc⟩ := exists_model_diagonal_scalars K d hdD
  obtain ⟨x,hx⟩ := CFSGFFourRelativeScalarIndex.powerHom_surjective (G:=Kˣ) c
  have hfixed : ∀i t,
      ((modelProductTorusHom K x)⁻¹*d)*modelRoot CartanMatrix.F₄ K false i t*
        ((modelProductTorusHom K x)⁻¹*d)⁻¹=modelRoot CartanMatrix.F₄ K false i t := by
    intro i t
    apply quotient_fixes_of_same_conjugation
    rw [hc,model_product_torus_action]
    simp only [Bool.false_eq_true,if_false,hx]
    congr 1
    exact mul_comm _ _
  have he := model_diagonal_eq_one_of_simple_fixed K ((modelProductTorusHom K x)⁻¹*d)
    ((modelDiagonalPart K).mul_mem
      ((modelDiagonalPart K).inv_mem (modelProductTorus_mem_diagonal K x)) hdD) hfixed
  refine ⟨x,?_⟩
  have h := congrArg (fun z : Model CartanMatrix.F₄ K=>modelProductTorusHom K x*z) he
  simpa only [mul_inv_cancel_left,mul_one] using h

theorem modelDiagonalPart_eq_productTorus_range :
    modelDiagonalPart K=(modelProductTorusHom K).range := by
  ext d
  constructor
  · intro hdD
    obtain ⟨x,hx⟩ := exists_model_diagonal_torus K d hdD
    exact ⟨x,hx.symm⟩
  · rintro ⟨x,rfl⟩
    exact modelProductTorus_mem_diagonal K x

end SymmetricSubgroupAsymptotics.CFSGFFourOriginalDiagonalTorus
