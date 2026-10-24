import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleCubicCurveWords
import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleCentralExtensionData
import SymmetricSubgroupAsymptotics.ExactHomSubgroupCardinality

/-! Actual fixed-word lifting of all four middle coordinates for fields
with at least four elements, including characteristic three. Cubic curve
words and their additive first-coordinate homomorphism provide the lifts.
The exact q^5 order follows from the proved actual highest-root kernel. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleCubicFixedLifts

open CFSGGTwoD4GeckMiddleFixedRadicalCoordinates CFSGGTwoD4GeckMiddleCubicCurveWords
open CFSGGTwoD4GeckMiddleFixedCoordinates CFSGGTwoD4GeckMiddleCentralExtensionData
open CFSGFiniteFieldPolynomialCurveSpan

def curveElement (K : Type) [Field K] (b t : K) : fixedMiddle K :=
  ⟨curveWord K b t,curveWord_mem_fixedMiddle K b t⟩

theorem projection_curveElement (K : Type) [Field K] [Finite K] (b t : K) :
    projection K (curveElement K b t) = Multiplicative.ofAdd (b • monomialCurve K 4 t) := by
  apply congrArg Multiplicative.ofAdd
  apply fixedCubeEmbedding_injective K
  apply Subtype.ext
  have hsmul := congrArg Subtype.val ((fixedCubeEmbedding K).map_smul b (monomialCurve K 4 t))
  exact (coordinate_spec K (curveElement K b t)).trans ((curveWord_firstLayer K b t).trans hsmul.symm)

theorem projection_surjective_of_card_four (K : Type) [Field K] [Finite K] (hcard : 4 ≤ Nat.card K) :
    Function.Surjective (projection K) := by
  have hspan := monomialCurve_span_eq_top K 4 (by decide) hcard
  have hlift : ∀ (b t : K), ∃ u : fixedMiddle K,
      projection K u = Multiplicative.ofAdd (b • monomialCurve K 4 t) :=
    fun b t => ⟨curveElement K b t,projection_curveElement K b t⟩
  intro c
  exact CFSGAdditiveImageScalarSpan.span_lifts (projection K) (monomialCurve K 4) hlift c.toAdd
    (by rw [hspan]; trivial)

theorem fixedMiddle_card_of_card_four (K : Type) [Field K] [Finite K] (hcard : 4 ≤ Nat.card K) :
    Nat.card (fixedMiddle K) = Nat.card K^5 := by
  have he := ExactHomSubgroupCardinality.card_comap_mul_card_map (projection K) (central K)
    (central_injective K) (central_range K) (⊤ : Subgroup (fixedMiddle K))
  rw [Subgroup.comap_top,Subgroup.map_top_of_surjective _ (projection_surjective_of_card_four K hcard),
    Subgroup.card_top,Subgroup.card_top,Subgroup.card_top] at he
  change Nat.card K*Nat.card (Fin 4 → K) = Nat.card (fixedMiddle K) at he
  rw [Nat.card_fun,Nat.card_fin] at he
  exact he.symm.trans (pow_succ' (Nat.card K) 4).symm

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleCubicFixedLifts
