import SymmetricSubgroupAsymptotics.CFSGFFourOriginalMiddleScalarColumn
import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalNegativeMiddleField
import Mathlib.Tactic.Ring

/-! The actual original-source column and genuine diagonal residual
kill the remaining negative middle scalar. The full signed middle field
action follows from the already proved native torus-normalizer rigidity. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalSignedMiddleField
open CFSGFFourOriginalMiddleScalarColumn CFSGReeFFourMiddleScalarResidual
open CFSGReeFFourOriginalNegativeMiddleField CFSGReeFFourOriginalNegativeMiddleRestriction
open CFSGReeFFourOriginalNegativeMiddleCoordinates CFSGReeFFourFieldParameters
open CFSGReeFFourOriginalPairRestriction CFSGReeFFourOriginalPositiveNormalization

private theorem unit_eq_one_of_add_sq_zero {K : Type*} [Field K] [CharP K 2]
    (c : Kˣ) (hc : (c : K)+(c : K)^2=0) : c=1 := by
  have hzero : (c : K)*((c : K)+1)=0 := by
    calc
      _=(c : K)+(c : K)^2 := by ring
      _=0 := hc
  have hs : (c : K)+1=0 := (mul_eq_zero.mp hzero).resolve_left c.ne_zero
  apply Units.ext
  change (c : K)=1
  calc
    (c : K)=(c : K)+(1+1) := by rw [CharTwo.add_self_eq_zero,add_zero]
    _=((c : K)+1)+1 := (add_assoc _ _ _).symm
    _=1 := by rw [hs,zero_add]

theorem negative_middle_scalar_eq_one (m : ℕ) (hm : 0<m) (f : pairStabilizer m hm)
    (tau : Field m ≃+* Field m) (hfields : positiveLayerDescription m hm f tau tau)
    (c : (Field m)ˣ)
    (hc : negativeMiddleAction m hm f (CFSGSuzukiUnipotent.coordinateElement m 1 0)=
      CFSGSuzukiUnipotent.coordinateElement m (c : Field m) 0) : c=1 := by
  have hz := middleScalarResidual_matrix_entry_zero m hm f tau hfields (c : Field m) hc
  have he := original_middleResidual_entry m (c : Field m)
  exact unit_eq_one_of_add_sq_zero c (he.symm.trans hz)

theorem negativeMiddleAction_eq_fieldAut (m : ℕ) (hm : 0<m) (f : pairStabilizer m hm)
    (tau : Field m ≃+* Field m) (hfields : positiveLayerDescription m hm f tau tau) :
    negativeMiddleAction m hm f=CFSGSuzukiUnipotentFieldActions.fieldAut m tau := by
  obtain ⟨c,hscaled,hcoord⟩ := exists_negative_middle_scaled_common_field m hm f tau hfields
  have hec := negative_middle_scalar_eq_one m hm f tau hfields c hcoord
  subst c
  simpa only [inv_one,map_one,one_mul] using hscaled

theorem original_negative_middle_field_action (m : ℕ) (hm : 0<m) (f : pairStabilizer m hm)
    (tau : Field m ≃+* Field m) (hfields : positiveLayerDescription m hm f tau tau)
    (a b : Field m) :
    f.val (originalNegativeMiddleEmbedding m hm (CFSGSuzukiUnipotent.coordinateElement m a b))=
      originalNegativeMiddleEmbedding m hm (CFSGSuzukiUnipotent.coordinateElement m (tau a) (tau b)) := by
  have he := negativeMiddleAction_embedding m hm f (CFSGSuzukiUnipotent.coordinateElement m a b)
  rw [negativeMiddleAction_eq_fieldAut m hm f tau hfields,
    CFSGSuzukiUnipotentFieldActions.fieldAut_coordinate] at he
  exact he.symm

end SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalSignedMiddleField
