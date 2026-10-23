import SymmetricSubgroupAsymptotics.CFSGGTwoOriginalPositiveRootWords
import SymmetricSubgroupAsymptotics.CFSGGTwoOriginalExceptionalModel

/-! Exact exceptional images of the two differently oriented ORIGINAL
Weyl words. Each maps to the OTHER INVERSE. The resulting higher-word
expression is recorded before any signed higher-root identification. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoOriginalExceptionalWeylWords
open CFSG.Models.Chevalley CFSGSerreModelRootGeneration CFSGGTwoSerreMatrices
open CFSGGTwoPositiveDirections CFSGGTwoOriginalPositiveRootWords
open CFSGGTwoOriginalExceptionalModel CFSGGTwoOriginalExceptionalRootCovariance
variable (K : Type) [Field K] [Finite K] [CharP K 3]
local notation "A" => CartanMatrix.G₂

theorem exceptional_shortWord :
    exceptionalModelEquiv K (shortWord K)=(longWord K)⁻¹ := by
  have hm : (-1:K)^3=-1 := by ring
  simp only [shortWord,map_mul,exceptionalModelEquiv_root]
  change modelRoot A K false 1 ((1:K)^3) * modelRoot A K true 1 ((-1:K)^3) *
      modelRoot A K false 1 ((1:K)^3)=(longWord K)⁻¹
  rw [one_pow,hm]
  simp only [longWord,mul_inv_rev,modelRoot_inv,neg_neg,mul_assoc]

theorem exceptional_longWord :
    exceptionalModelEquiv K (longWord K)=(shortWord K)⁻¹ := by
  simp only [longWord,map_mul,exceptionalModelEquiv_root]
  change modelRoot A K false 0 (-1) * modelRoot A K true 0 1 *
      modelRoot A K false 0 (-1)=(shortWord K)⁻¹
  simp only [shortWord,mul_inv_rev,modelRoot_inv,neg_neg,mul_assoc]

def reflectedModel (j : Fin 6) : Model A K :=
  match j.val with
  | 0 => 1
  | 1 => 1
  | 2 => (shortWord K)⁻¹
  | 3 => (longWord K)⁻¹ * (shortWord K)⁻¹
  | 4 => (longWord K)⁻¹
  | _ => (shortWord K)⁻¹ * (longWord K)⁻¹

theorem exceptional_directionModel (j : Fin 6) :
    exceptionalModelEquiv K (directionModel K j)=reflectedModel K j := by
  fin_cases j
  · exact map_one (exceptionalModelEquiv K)
  · exact map_one (exceptionalModelEquiv K)
  · exact exceptional_longWord K
  · change exceptionalModelEquiv K (shortWord K * longWord K)=
      (longWord K)⁻¹ * (shortWord K)⁻¹
    rw [map_mul,exceptional_shortWord,exceptional_longWord]
  · exact exceptional_shortWord K
  · change exceptionalModelEquiv K (longWord K * shortWord K)=
      (shortWord K)⁻¹ * (longWord K)⁻¹
    rw [map_mul,exceptional_longWord,exceptional_shortWord]

theorem exceptional_positiveModel_expression (j : Fin 6) (t : K) :
    exceptionalModelEquiv K (positiveModel K j t)=
      reflectedModel K j *
        modelRoot A K false (exchangedNode (rootNode j))
          (exceptionalParameter K (rootNode j) t) * (reflectedModel K j)⁻¹ := by
  rw [positiveModel,map_mul,map_mul,map_inv,exceptional_directionModel,
    exceptionalModelEquiv_root]

end SymmetricSubgroupAsymptotics.CFSGGTwoOriginalExceptionalWeylWords
