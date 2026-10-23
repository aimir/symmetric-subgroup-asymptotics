import SymmetricSubgroupAsymptotics.CFSGGTwoPositiveActionCoordinates
import SymmetricSubgroupAsymptotics.CFSGGTwoOriginalPositiveRootWords

/-! Division-free six-word coordinates for the literal positive root
words. Six sparse entries recover all six parameters, over every
commutative ring. The source Model word has exactly this native image.
No equality of a full positive subgroup with these words is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGGTwoPositiveSixWord
open CFSG.Models.Chevalley CFSGGTwoSerreMatrices CFSGGTwoPositiveDirections
open CFSGGTwoPositiveRootMatrices CFSGGTwoPositiveWordActions CFSGGTwoPositiveActionCoordinates
open CFSGGTwoOriginalPositiveRootWords CFSGGTwoOriginalNaturalEquivalence
variable (R : Type*) [CommRing R]

def matrixWord (a : Fin 6 → R) : Mat R :=
  polynomialRoot R 0 (a 0)*polynomialRoot R 1 (a 1)*
    polynomialRoot R 2 (a 2)*polynomialRoot R 3 (a 3)*
      polynomialRoot R 4 (a 4)*polynomialRoot R 5 (a 5)

theorem matrixWord_apply (a : Fin 6 → R) (v : Index → R) :
    matrixWord R a *ᵥ v=
      action0 R (a 0) (action1 R (a 1) (action2 R (a 2)
        (action3 R (a 3) (action4 R (a 4) (action5 R (a 5) v))))) := by
  simp only [matrixWord,←Matrix.mulVec_mulVec,polynomialRoot_apply,
    positiveAction_0,positiveAction_1,positiveAction_2,positiveAction_3,positiveAction_4,positiveAction_5]

theorem entry_01 (a : Fin 6 → R) :
    matrixWord R a (pos 0) (pos 1)=a 0 := by
  calc
    _=(matrixWord R a *ᵥ Pi.single (pos 1) 1) (pos 0) :=
      (congrFun (Matrix.mulVec_single_one (matrixWord R a) (pos 1)) (pos 0)).symm
    _=_ := by
      rw [matrixWord_apply]
      simp only [action0_pos0,action1_pos0,action1_pos1,action2_pos0,action2_pos1,action2_pos2,action3_neg1,action3_neg3,action3_pos0,action3_pos1,action3_pos2,action3_pos3,action4_neg0,action4_neg1,action4_neg2,action4_neg3,action4_pos0,action4_pos1,action4_pos2,action4_pos3,action5_neg0,action5_neg1,action5_neg2,action5_neg3,action5_pos0,action5_pos1,action5_pos2,action5_pos3]
      simp [Pi.single_apply,Function.update,pos,neg,Fin.ext_iff] <;> ring

theorem entry_12 (a : Fin 6 → R) :
    matrixWord R a (pos 1) (pos 2)=a 1 := by
  calc
    _=(matrixWord R a *ᵥ Pi.single (pos 2) 1) (pos 1) :=
      (congrFun (Matrix.mulVec_single_one (matrixWord R a) (pos 2)) (pos 1)).symm
    _=_ := by
      rw [matrixWord_apply]
      simp only [action0_pos1,action1_pos1,action2_pos1,action2_pos2,action3_neg1,action3_neg3,action3_pos1,action3_pos2,action3_pos3,action4_neg0,action4_neg1,action4_neg2,action4_neg3,action4_pos1,action4_pos2,action4_pos3,action5_neg0,action5_neg1,action5_neg2,action5_neg3,action5_pos1,action5_pos2,action5_pos3]
      simp [Pi.single_apply,Function.update,pos,neg,Fin.ext_iff] <;> ring

theorem entry_02 (a : Fin 6 → R) :
    matrixWord R a (pos 0) (pos 2)=a 0*a 1+a 2 := by
  calc
    _=(matrixWord R a *ᵥ Pi.single (pos 2) 1) (pos 0) :=
      (congrFun (Matrix.mulVec_single_one (matrixWord R a) (pos 2)) (pos 0)).symm
    _=_ := by
      rw [matrixWord_apply]
      simp only [action0_pos0,action1_pos0,action1_pos1,action2_pos0,action2_pos1,action2_pos2,action3_neg1,action3_neg3,action3_pos0,action3_pos1,action3_pos2,action3_pos3,action4_neg0,action4_neg1,action4_neg2,action4_neg3,action4_pos0,action4_pos1,action4_pos2,action4_pos3,action5_neg0,action5_neg1,action5_neg2,action5_neg3,action5_pos0,action5_pos1,action5_pos2,action5_pos3]
      simp [Pi.single_apply,Function.update,pos,neg,Fin.ext_iff] <;> ring

theorem entry_03 (a : Fin 6 → R) :
    matrixWord R a (pos 0) (pos 3)=-a 0*a 2+a 3 := by
  calc
    _=(matrixWord R a *ᵥ Pi.single (pos 3) 1) (pos 0) :=
      (congrFun (Matrix.mulVec_single_one (matrixWord R a) (pos 3)) (pos 0)).symm
    _=_ := by
      rw [matrixWord_apply]
      simp only [action0_pos0,action1_pos0,action1_pos1,action2_pos0,action2_pos1,action2_pos2,action3_neg1,action3_neg3,action3_pos0,action3_pos1,action3_pos2,action3_pos3,action4_neg0,action4_neg1,action4_neg2,action4_neg3,action4_pos0,action4_pos1,action4_pos2,action4_pos3,action5_neg0,action5_neg1,action5_neg2,action5_neg3,action5_pos0,action5_pos1,action5_pos2,action5_pos3]
      simp [Pi.single_apply,Function.update,pos,neg,Fin.ext_iff] <;> ring

theorem entry_06 (a : Fin 6 → R) :
    matrixWord R a (pos 0) (neg 2)=a 0*a 3-a 4 := by
  calc
    _=(matrixWord R a *ᵥ Pi.single (neg 2) 1) (pos 0) :=
      (congrFun (Matrix.mulVec_single_one (matrixWord R a) (neg 2)) (pos 0)).symm
    _=_ := by
      rw [matrixWord_apply]
      simp only [action0_pos0,action1_pos0,action1_pos1,action2_pos0,action2_pos1,action2_pos2,action3_neg1,action3_neg3,action3_pos0,action3_pos1,action3_pos2,action3_pos3,action4_neg0,action4_neg1,action4_neg2,action4_neg3,action4_pos0,action4_pos1,action4_pos2,action4_pos3,action5_neg0,action5_neg1,action5_neg2,action5_neg3,action5_pos0,action5_pos1,action5_pos2,action5_pos3]
      simp [Pi.single_apply,Function.update,pos,neg,Fin.ext_iff] <;> ring

theorem entry_05 (a : Fin 6 → R) :
    matrixWord R a (pos 0) (neg 1)=-a 0*a 1*a 3-a 0*(a 2)^2-a 2*a 3+a 5 := by
  calc
    _=(matrixWord R a *ᵥ Pi.single (neg 1) 1) (pos 0) :=
      (congrFun (Matrix.mulVec_single_one (matrixWord R a) (neg 1)) (pos 0)).symm
    _=_ := by
      rw [matrixWord_apply]
      simp only [action0_pos0,action1_pos0,action1_pos1,action2_pos0,action2_pos1,action2_pos2,action3_neg1,action3_neg3,action3_pos0,action3_pos1,action3_pos2,action3_pos3,action4_neg0,action4_neg1,action4_neg2,action4_neg3,action4_pos0,action4_pos1,action4_pos2,action4_pos3,action5_neg0,action5_neg1,action5_neg2,action5_neg3,action5_pos0,action5_pos1,action5_pos2,action5_pos3]
      simp [Pi.single_apply,Function.update,pos,neg,Fin.ext_iff] <;> ring

theorem matrixWord_injective : Function.Injective (matrixWord R) := by
  intro a b hab
  have h0 : matrixWord R a (pos 0) (pos 1)=
      matrixWord R b (pos 0) (pos 1) :=
    congrArg (fun M : Mat R => M (pos 0) (pos 1)) hab
  simp only [entry_01] at h0
  have h1 : matrixWord R a (pos 1) (pos 2)=
      matrixWord R b (pos 1) (pos 2) :=
    congrArg (fun M : Mat R => M (pos 1) (pos 2)) hab
  simp only [entry_12] at h1
  have h2 : matrixWord R a (pos 0) (pos 2)=
      matrixWord R b (pos 0) (pos 2) :=
    congrArg (fun M : Mat R => M (pos 0) (pos 2)) hab
  simp only [entry_02,h0,h1] at h2
  have h2 : a 2=b 2 := add_left_cancel h2
  have h3 : matrixWord R a (pos 0) (pos 3)=
      matrixWord R b (pos 0) (pos 3) :=
    congrArg (fun M : Mat R => M (pos 0) (pos 3)) hab
  simp only [entry_03,h0,h2] at h3
  have h3 : a 3=b 3 := add_left_cancel h3
  have h4n : matrixWord R a (pos 0) (neg 2)=
      matrixWord R b (pos 0) (neg 2) :=
    congrArg (fun M : Mat R => M (pos 0) (neg 2)) hab
  simp only [entry_06,h0,h3,sub_eq_add_neg] at h4n
  have h4 : a 4=b 4 := neg_injective (add_left_cancel h4n)
  have h5 : matrixWord R a (pos 0) (neg 1)=
      matrixWord R b (pos 0) (neg 1) :=
    congrArg (fun M : Mat R => M (pos 0) (neg 1)) hab
  simp only [entry_05,h0,h1,h2,h3] at h5
  have h5 : a 5=b 5 := add_left_cancel h5
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5

def positiveWord (K : Type) [Field K] (a : Fin 6 → K) : (Mat K)ˣ :=
  positiveRoot K 0 (a 0)*positiveRoot K 1 (a 1)*positiveRoot K 2 (a 2)*
    positiveRoot K 3 (a 3)*positiveRoot K 4 (a 4)*positiveRoot K 5 (a 5)

theorem positiveWord_val (K : Type) [Field K] (a : Fin 6 → K) :
    (positiveWord K a : Mat K)=matrixWord K a := by
  change (positiveWord K a : Mat K)=
    polynomialRoot K 0 (a 0)*polynomialRoot K 1 (a 1)*
      polynomialRoot K 2 (a 2)*polynomialRoot K 3 (a 3)*
        polynomialRoot K 4 (a 4)*polynomialRoot K 5 (a 5)
  simp only [positiveWord,Units.val_mul,positiveRoot_val]

theorem positiveWord_injective (K : Type) [Field K] : Function.Injective (positiveWord K) := by
  intro a b h
  apply matrixWord_injective K
  have he := congrArg (fun u : (Mat K)ˣ => (u:Mat K)) h
  simpa only [positiveWord_val] using he

def modelWord (K : Type) [Field K] (a : Fin 6 → K) : Model CartanMatrix.G₂ K :=
  positiveModel K 0 (a 0)*positiveModel K 1 (a 1)*positiveModel K 2 (a 2)*
    positiveModel K 3 (a 3)*positiveModel K 4 (a 4)*positiveModel K 5 (a 5)

theorem modelWord_native (K : Type) [Field K] (a : Fin 6 → K) :
    (modelEquivNatural K (modelWord K a)).val=positiveWord K a := by
  simp only [modelWord,map_mul,positiveModel_native]
  rfl

theorem modelWord_injective (K : Type) [Field K] : Function.Injective (modelWord K) := by
  intro a b h
  apply positiveWord_injective K
  have he := congrArg (fun g : Model CartanMatrix.G₂ K => (modelEquivNatural K g).val) h
  simpa only [modelWord_native] using he

end SymmetricSubgroupAsymptotics.CFSGGTwoPositiveSixWord
