import SymmetricSubgroupAsymptotics.CFSGSerreFiniteRootActionTable
import SymmetricSubgroupAsymptotics.CFSGFFourOriginalHeightFourLowering

/-! A selected first application of the coefficient-table induction.
The non-root raise E0(v11) vanishes: its positive H0 weight is three,
and its F0 lowering is the finite coefficient cancellation -v11+v11.
All input lowerings/raises are previously proved original source
identities. No family basis or matrix faithfulness premise is added. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGFFourOriginalRootActionTablePilot
open CFSG.Models.Chevalley CFSGSerreSignedRootWeights CFSGSerreFiniteRootActionTable
open CFSGFFourOriginalFiftyTwoFamily CFSGFFourOriginalHeightThreeRaising
open CFSGFFourOriginalHeightFourRaising CFSGFFourOriginalHeightFourLowering
local notation "A" => CartanMatrix.F₄
local notation "L" => RationalLie A

theorem raising_zero_eleven (neg:Bool) :
    ⁅rootVector A neg 0,(rootVectors neg 11).val⁆=0 := by
  let x:Fin 24→L:=fun j=>(rootVectors neg j).val
  let d:Fin 24→ℚ:=Pi.single 7 (-1)
  let e:Fin 24→Fin 24→ℚ:=fun _=>Pi.single 11 (-1)
  have hc:simpleWeight (0:Fin 4) (11:Fin 24)=1:=by decide +kernel
  have hw:⁅coroot A neg 0,x 11⁆=(1:ℚ) • x 11 := by
    simpa only [x,hc,Int.cast_one] using rootVectors_weight neg 0 11
  have hd:⁅oppositeVector A neg 0,x 11⁆=Fintype.linearCombination ℚ x d := by
    have h:=opposite_eleven neg 0
    change ⁅oppositeVector A neg 0,(rootVectors neg 11).val⁆= -(rootVectors neg 7).val at h
    simpa only [x,d,Fintype.linearCombination_apply_single,neg_one_smul] using h
  have he:∀l,d l≠0→⁅rootVector A neg 0,x l⁆=Fintype.linearCombination ℚ x (e l) := by
    intro l hl
    have hindex:l=(7:Fin 24) := by
      by_contra hn
      apply hl
      simp [d,Pi.single_apply,hn,Ne.symm hn]
    subst l
    have h:=raising_seven neg 0
    change ⁅rootVector A neg 0,(rootVectors neg 7).val⁆= -(rootVectors neg 11).val at h
    simpa only [x,e,Fintype.linearCombination_apply_single,neg_one_smul] using h
  have ht:⁅oppositeVector A neg 0,(0:L)⁆=Fintype.linearCombination ℚ x (0:Fin 24→ℚ) := by
    rw [lie_zero,map_zero]
  have hcoeff:(if (0:Fin 4)=0 then (-1:ℚ) • Pi.single (11:Fin 24) 1 else 0)+
      (∑l,d l • e l)=(0:Fin 24→ℚ) := by
    funext m
    by_cases hm:(11:Fin 24)=m <;>
      simp [d,e,Pi.single_apply,Finset.sum_apply,ite_smul,Finset.sum_ite_eq',
        smul_eq_mul,hm]
  exact raising_eq_of_lowering_coefficients A x neg 0 0 (by decide) 11 1
    (by change 0<(2:ℚ)+1; norm_num) 0 hw
    (by rw [lie_zero,smul_zero]) d e 0 hd he ht hcoeff

end SymmetricSubgroupAsymptotics.CFSGFFourOriginalRootActionTablePilot
