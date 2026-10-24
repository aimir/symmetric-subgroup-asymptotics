import SymmetricSubgroupAsymptotics.CFSGUnitaryRankOneFixedScalarAction
import SymmetricSubgroupAsymptotics.CFSGUnitaryRadicalNormalizerAction
import SymmetricSubgroupAsymptotics.CFSGTwistedA2FixedField
import SymmetricSubgroupAsymptotics.CentralExtensionLayerOrbitIndex

/-! A genuine determinant-one matrix chart over the literal fixed
field supplies q^2(q-1) distinct images of every nonsingular vector.
Only actual middle elements in the SAME radical normalizer are used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent CFSGTwistedA2FixedField
open CentralExtensionLayerOrbitIndex

private def slTwoUnitLowerChart {F : Type*} [Field F] (p : (F × F) × Fˣ) :
    Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![p.1.1,(p.1.1*p.1.2-1)/(p.2 : F); (p.2 : F),p.1.2], by
    rw [Matrix.det_fin_two]
    change p.1.1 * p.1.2 - ((p.1.1 * p.1.2 - 1) / (p.2 : F)) * (p.2 : F) = 1
    field_simp [Units.ne_zero p.2] <;> ring⟩

private theorem slTwoUnitLowerChart_injective {F : Type*} [Field F] :
    Function.Injective (slTwoUnitLowerChart (F := F)) := by
  rintro ⟨⟨a,c⟩,b⟩ ⟨⟨a',c'⟩,b'⟩ he
  have ha := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) F => A.val 0 0) he
  have hc := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) F => A.val 1 1) he
  have hb := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) F => A.val 1 0) he
  change a = a' at ha
  change c = c' at hc
  change (b : F) = (b' : F) at hb
  exact Prod.ext (Prod.ext ha hc) (Units.ext hb)

private theorem rankOneScalarFixedHom_injective (q : CFSG.PrimePower) :
    Function.Injective (rankOneScalarFixedHom q) := by
  intro A B he
  apply Subtype.ext
  ext i j
  have hh := congrArg (fun g : naturalFixed 1 q => (g.val.val : Mat (q.Extension 2) 1) i j) he
  simpa only [rankOneScalarFixedHom_matrix, Matrix.map_apply] using hh

theorem rankOne_nonisotropic_normalizer_orbit_card (q : CFSG.PrimePower)
    (v : Fin 2 → q.Extension 2) (hv : unitaryNaturalPair q 1 v v ≠ 0) :
    q.order ^ 2 * (q.order - 1) ≤
      Nat.card (layerOrbit (unitaryRadicalNormalizerVectorAutHom q 1) (Multiplicative.ofAdd v)) := by
  let P := ((rankOneFixedField q × rankOneFixedField q) × (rankOneFixedField q)ˣ)
  let g (p : P) := rankOneScalarFixedHom q (slTwoUnitLowerChart p)
  let f : P → layerOrbit (unitaryRadicalNormalizerVectorAutHom q 1) (Multiplicative.ofAdd v) :=
    fun p => ⟨Multiplicative.ofAdd ((g p).val.val *ᵥ v), by
      refine ⟨middleRadicalNormalizerHom q 1 (g p), ?_⟩
      rw [middleRadicalNormalizer_vector_action, naturalVectorMulAutHom_apply]
      simp only [toAdd_ofAdd]⟩
  have hf : Function.Injective f := by
    intro p t he
    apply slTwoUnitLowerChart_injective
    apply rankOneScalarFixedHom_injective q
    apply rankOne_nonisotropic_action_injective q v hv
    exact congrArg (fun w :
      layerOrbit (unitaryRadicalNormalizerVectorAutHom q 1) (Multiplicative.ofAdd v) =>
        w.val.toAdd) he
  have hF : Nat.card (rankOneFixedField q) = q.order := fixedField_card q
  have hP : Nat.card P = q.order ^ 2 * (q.order - 1) := by
    simp only [P, Nat.card_prod, Nat.card_units, hF, pow_two, mul_assoc]
  rw [← hP]
  exact Nat.card_le_card_of_injective f hf

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
