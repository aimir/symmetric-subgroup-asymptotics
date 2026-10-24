import SymmetricSubgroupAsymptotics.CFSGFFourOriginalUnitLoweringPaths
import SymmetricSubgroupAsymptotics.CFSGFFourOriginalSeparatingCartan
import SymmetricSubgroupAsymptotics.CFSGRationalLieWeightCoordinates

/-! Actual rational separating-Cartan weights on the original52 source
vectors and their lowering words. The resulting coordinate crosszero
proof is performed before integer casting and finite-field reduction. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGFFourOriginalSourceWordWeights
open CFSG.Models.Chevalley CFSGSerreSignedRootWeights
open CFSGFFourOriginalFiftyTwoFamily CFSGFFourOriginalRootFamilyProfile
open CFSGFFourOriginalUnitLoweringPaths CFSGFFourOriginalSeparatingCartan
open CFSGRationalLieWeightCoordinates
local notation "A" => CartanMatrix.F₄

def signedTestWeight (neg:Bool) (j:Fin 24) : ℤ:=if neg then -testWeight j else testWeight j

def fullWeight : BasisIndex→ℤ
  | .inl (neg,j)=>signedTestWeight neg j
  | .inr _=>0

theorem root_weight (neg:Bool) (j:Fin 24) :
    ⁅testCartan,(rootVectors neg j).val⁆=
      (signedTestWeight neg j:ℚ) • (rootVectors neg j).val := by
  cases neg
  · exact testCartan_weight j
  · have hb (b:Fin 4) :
        ⁅generator A (.H b),(rootVectors true j).val⁆=
          (-(simpleWeight b j:ℚ)) • (rootVectors true j).val := by
      have h:=rootVectors_weight true b j
      change ⁅-generator A (.H b),(rootVectors true j).val⁆=
        (simpleWeight b j:ℚ) • (rootVectors true j).val at h
      have hn:=congrArg (fun z:RationalLie A=> -z) h
      simpa only [neg_lie,neg_neg,neg_smul] using hn
    change ⁅∑b:Fin 4,(coefficients b:ℚ) • generator A (.H b),(rootVectors true j).val⁆=
      ((-testWeight j:ℤ):ℚ) • (rootVectors true j).val
    rw [sum_lie]
    simp only [smul_lie,hb,smul_smul]
    rw [←Finset.sum_smul]
    congr 1
    simp only [testWeight,Int.cast_neg,Int.cast_sum,Int.cast_mul,mul_neg,Finset.sum_neg_distrib]

theorem family_weight (j:BasisIndex) :
    ⁅testCartan,vectors j⁆=(fullWeight j:ℚ) • vectors j := by
  cases j with
  | inl z=>exact root_weight z.1 z.2
  | inr b=>
    change ⁅testCartan,generator A (.H b)⁆=(0:ℚ) • generator A (.H b)
    rw [zero_smul,testCartan,sum_lie]
    apply Finset.sum_eq_zero
    intro i hi
    rw [smul_lie]
    have hh:⁅coroot A false i,generator A (.H b)⁆=0:=coroots_commute A false i b
    rw [hh,smul_zero]

theorem simple_weight (neg:Bool) (i:Fin 4) :
    ⁅testCartan,rootVector A neg i⁆=
      (signedTestWeight neg (simpleIndex i):ℚ) • rootVector A neg i := by
  have h:=root_weight neg (simpleIndex i)
  change ⁅testCartan,family neg (.inl (simpleIndex i))⁆=
    (signedTestWeight neg (simpleIndex i):ℚ) • family neg (.inl (simpleIndex i)) at h
  simpa only [simple_value] using h

def wordShift (neg:Bool) (ss:List (Fin 4)) : ℤ:=
  (ss.map (fun i=>signedTestWeight neg (simpleIndex i))).sum

theorem word_weight (neg:Bool) (ss:List (Fin 4)) (x:RationalLie A) (mu:ℚ)
    (hx:⁅testCartan,x⁆=mu • x) :
    ⁅testCartan,wordOperator neg ss x⁆=
      (mu+(wordShift neg ss:ℚ)) • wordOperator neg ss x := by
  induction ss generalizing x mu with
  | nil=>simpa only [wordOperator,Module.End.one_apply,wordShift,List.map_nil,
      List.sum_nil,Int.cast_zero,add_zero] using hx
  | cons i ss ih=>
    have hs:=bracket_weight testCartan (rootVector A neg i) x
      (signedTestWeight neg (simpleIndex i):ℚ) mu (simple_weight neg i) hx
    have h:=ih ⁅rootVector A neg i,x⁆ ((signedTestWeight neg (simpleIndex i):ℚ)+mu) hs
    simpa only [wordOperator,Module.End.mul_apply,LieAlgebra.ad_apply,wordShift,
      List.map_cons,List.sum_cons,Int.cast_add,add_assoc,add_comm,add_left_comm] using h

theorem lowering_weight_balance : ∀(neg:Bool)(j:Fin 24),
    signedTestWeight neg j+wordShift (!neg) (loweringSteps j)=
      signedTestWeight neg (simpleIndex (terminalNode j)) := by decide +kernel

theorem signedTestWeight_ne_zero (neg:Bool) (j:Fin 24) : signedTestWeight neg j≠0 := by
  have h:=testWeight_positive j
  cases neg
  · change testWeight j≠0
    omega
  · change -testWeight j≠0
    omega

theorem signedTestWeight_injective :
    Function.Injective (fun z:Bool×Fin 24=>signedTestWeight z.1 z.2) := by
  rintro ⟨s,j⟩ ⟨t,k⟩ h
  have hj:=testWeight_positive j
  have hk:=testWeight_positive k
  cases s <;> cases t
  · exact congrArg (fun x:Fin 24=>(false,x)) (testWeight_injective h)
  · change testWeight j= -testWeight k at h
    omega
  · change -testWeight j=testWeight k at h
    omega
  · change -testWeight j= -testWeight k at h
    exact congrArg (fun x:Fin 24=>(true,x)) (testWeight_injective (neg_injective h))

theorem fullWeight_eq_root_iff (neg:Bool) (j:Fin 24) (k:BasisIndex) :
    fullWeight k=signedTestWeight neg j ↔ k=.inl (neg,j) := by
  cases k with
  | inl z=>
    constructor
    · intro h
      exact congrArg Sum.inl (signedTestWeight_injective h)
    · intro h
      exact congrArg (fun z:Bool×Fin 24=>signedTestWeight z.1 z.2) (Sum.inl.inj h)
  | inr b=>
    constructor
    · intro h
      exact (signedTestWeight_ne_zero neg j h.symm).elim
    · intro h
      cases h

end SymmetricSubgroupAsymptotics.CFSGFFourOriginalSourceWordWeights
