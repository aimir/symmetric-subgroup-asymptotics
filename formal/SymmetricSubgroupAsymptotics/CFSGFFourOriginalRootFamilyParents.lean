import SymmetricSubgroupAsymptotics.CFSGFFourOriginalRootFamilyProfile
import SymmetricSubgroupAsymptotics.CFSGFFourOriginalHeightFivePaths
import SymmetricSubgroupAsymptotics.CFSGFFourOriginalHeightThreeRaising

/-! All twenty genuine nonsimple parent paths for the whole-family
source certificate. Seventeen are literal appended unit steps; the
three normalized middle/double steps retain coefficients -2,2,2.
Only finite path-list data is certified. No basis or image argument is
used to establish the original source equations. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFFourOriginalRootFamilyParents
open CFSG.Models.Chevalley CFSGSerreDividedPowerPaths CFSGSerreDividedPowerPathComposition
open CFSGFFourOriginalFiftyTwoFamily CFSGFFourOriginalHeightThreeRaising
open CFSGFFourOriginalHeightFivePaths CFSGFFourOriginalRootFamilyProfile
local notation "A" => CartanMatrix.F₄

def childIndex (t:Fin 20) : Fin 24:=⟨t.val+4,by omega⟩
def parentIndex (t:Fin 20) : Fin 24:=
  ![1,2,3,5,5,6,8,9,8,10,12,12,14,15,16,17,19,20,21,22] t
def parentNode (t:Fin 20) : Fin 4:=![3,2,1,3,1,2,3,3,0,2,3,0,2,3,1,2,1,1,2,3] t
def parentCoefficient (t:Fin 20) : ℤ:=![1,1,1,1,-2,1,1,1,1,1,1,2,1,1,1,1,1,2,1,1] t

theorem parent_height : ∀t:Fin 20,
    rootHeight (parentIndex t)+1=rootHeight (childIndex t) := by decide +kernel

theorem parent_coefficient_ne_zero : ∀t:Fin 20,parentCoefficient t≠0 := by decide +kernel

private theorem unit_parent_data : ∀t:Fin 20,parentCoefficient t=1→
    start (childIndex t)=start (parentIndex t) ∧
      steps (childIndex t)=steps (parentIndex t)++[(parentNode t,1)] := by decide +kernel

private theorem exceptional_parent_data : ∀t:Fin 20,parentCoefficient t≠1→
    t=4 ∨ t=11 ∨ t=17 := by decide +kernel

private theorem double_parent_twenty_one (neg:Bool) :
    ⁅rootVector A neg 1,(rootVectors neg 20).val⁆=(2:ℚ) • (rootVectors neg 21).val := by
  have h:=congrArg (fun z:integralLattice A=>z.val)
    (path_double_step A neg (start 19) (steps 19) 1)
  change dividedPower A neg 1 1 (rootVectors neg 20).val=
    (2:ℕ) • (rootVectors neg 21).val at h
  have hone:∀z:RationalLie A,dividedPower A neg 1 1 z=⁅rootVector A neg 1,z⁆:=by
    intro z
    simp [dividedPower]
  rw [hone] at h
  simpa only [two_smul] using h

theorem source_parent (neg:Bool) (t:Fin 20) :
    ⁅rootVector A neg (parentNode t),(rootVectors neg (parentIndex t)).val⁆=
      (parentCoefficient t:ℚ) • (rootVectors neg (childIndex t)).val := by
  by_cases hc:parentCoefficient t=1
  · obtain ⟨hs,ht⟩:=unit_parent_data t hc
    rw [hc,Int.cast_one,one_smul]
    change ⁅rootVector A neg (parentNode t),
      (pathVector A neg (start (parentIndex t)) (steps (parentIndex t))).val⁆=
      (pathVector A neg (start (childIndex t)) (steps (childIndex t))).val
    rw [hs,ht,path_append_one_val]
  · rcases exceptional_parent_data t hc with ht|ht|ht
    · subst t
      change ⁅rootVector A neg 1,(rootVectors neg 5).val⁆=(-2:ℚ) • (rootVectors neg 8).val
      exact raising_five neg 1
    · subst t
      change ⁅rootVector A neg 0,(rootVectors neg 12).val⁆=(2:ℚ) • (rootVectors neg 15).val
      exact raising_zero_twelve neg
    · subst t
      change ⁅rootVector A neg 1,(rootVectors neg 20).val⁆=(2:ℚ) • (rootVectors neg 21).val
      exact double_parent_twenty_one neg

end SymmetricSubgroupAsymptotics.CFSGFFourOriginalRootFamilyParents
