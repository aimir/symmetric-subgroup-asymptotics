import SymmetricSubgroupAsymptotics.CFSGUnitaryRankOneFixedScalarAction
import SymmetricSubgroupAsymptotics.CFSGUnitaryRankThreeTorusQuotientAction
import SymmetricSubgroupAsymptotics.CFSGUnitaryConjugateRatio
import SymmetricSubgroupAsymptotics.CentralExtensionLayerOrbitIndex

/-! Actual middle and paired-torus words give fixed-field column
charts in one literal radical-normalizer orbit. The scalar component is
the actual conjugate-ratio image; no full SU2 shell assertion is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent CFSGSerreOrdinaryTwists
open CentralExtensionLayerOrbitIndex

def rankOneFixedColumn (q : CFSG.PrimePower) :=
  {x : Fin 2 → rankOneFixedField q // x ≠ 0}

def rankOneScalarColumn (q : CFSG.PrimePower) (a : q.Extension 2)
    (x : rankOneFixedColumn q) : Fin 2 → q.Extension 2 := fun i => a * (x.val i : q.Extension 2)

theorem rankOneScalarColumn_injective (q : CFSG.PrimePower) (a : q.Extension 2) (ha : a ≠ 0) :
    Function.Injective (rankOneScalarColumn q a) := by
  intro x y he
  apply Subtype.ext
  funext i
  apply Subtype.ext
  exact mul_left_cancel₀ ha (congrFun he i)

theorem rankThree_normalizer_scalarColumn_mem (q : CFSG.PrimePower)
    (a : q.Extension 2) (u : (q.Extension 2)ˣ) (x : rankOneFixedColumn q) :
    Multiplicative.ofAdd (rankOneScalarColumn q ((definingFieldAutomorphism q 2 u / u) * a) x) ∈
      layerOrbit (unitaryRadicalNormalizerVectorAutHom q 1)
        (Multiplicative.ofAdd (Pi.single (0 : Fin 2) a)) := by
  obtain ⟨g, hg⟩ := exists_rankOneFixed_first_column q x.val x.property
  have ht : unitaryRadicalNormalizerVectorAutHom q 1 (rankThreeTorusNormalizer q u)
      (Multiplicative.ofAdd (Pi.single (0 : Fin 2) a)) =
        Multiplicative.ofAdd (Pi.single (0 : Fin 2) ((definingFieldAutomorphism q 2 u / u) * a)) := by
    apply Multiplicative.toAdd.injective
    rw [rankThreeTorusNormalizer_vector_action]
    ext i
    fin_cases i <;> simp
  refine ⟨middleRadicalNormalizerHom q 1 g * rankThreeTorusNormalizer q u, ?_⟩
  rw [map_mul]
  change unitaryRadicalNormalizerVectorAutHom q 1 (middleRadicalNormalizerHom q 1 g)
    (unitaryRadicalNormalizerVectorAutHom q 1 (rankThreeTorusNormalizer q u)
      (Multiplicative.ofAdd (Pi.single (0 : Fin 2) a))) = _
  rw [ht, middleRadicalNormalizer_vector_action, naturalVectorMulAutHom_apply]
  apply Multiplicative.toAdd.injective
  simp only [toAdd_ofAdd]
  funext i
  rw [Matrix.mulVec_single]
  change (g.val.val : Mat (q.Extension 2) 1) i 0 *
    ((definingFieldAutomorphism q 2 u / u) * a) = _
  rw [hg]
  exact mul_comm _ _

theorem rankThree_ratioRange_scalarColumn_mem (q : CFSG.PrimePower)
    (a : q.Extension 2) (z : (unitaryConjugateRatioHom q).range) (x : rankOneFixedColumn q) :
    Multiplicative.ofAdd (rankOneScalarColumn q ((z.val : q.Extension 2) * a) x) ∈
      layerOrbit (unitaryRadicalNormalizerVectorAutHom q 1)
        (Multiplicative.ofAdd (Pi.single (0 : Fin 2) a)) := by
  obtain ⟨u, hu⟩ := z.property
  rw [← hu, unitaryConjugateRatioHom_val]
  exact rankThree_normalizer_scalarColumn_mem q a u x

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
