import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckHeightData
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckStepMatrices
import SymmetricSubgroupAsymptotics.CFSGWeightedPermutationGram
import Mathlib.Tactic.Abel

/-! The opposite-root block of the actual Geck Gram form. Its skew
identity is proved from the literal root-step and height signs. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckRootGram
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoGeckColumns
open CFSGNormTwoGeckHeightData CFSGNormTwoGeckStepMatrices
variable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)]

def rootGram : Matrix (Roots A) (Roots A) ℚ :=
  CFSGWeightedPermutationGram.gram (negativePerm A hs hp) (rootSign A)

theorem rootGram_symmetric : (rootGram A hs hp).transpose=rootGram A hs hp := by
  apply CFSGWeightedPermutationGram.gram_symmetric
  · exact negativeIndex_involutive A hs hp
  · exact rootSign_negative A hs hp

private theorem flip_sum {V : Type*} [AddCommGroup V] (a j k : V)
    (h : -k=a+j) : -j=a+k := by
  have hz : a+j+k=0 := by rw [←h,neg_add_cancel]
  calc
    -j=(a+j+k)-j := by rw [hz,zero_sub]
    _=a+k := by abel

theorem root_step_skew (a : Roots A)
    (hshift : ∀ j k,(rootPairing A hs hp).root k=
      (rootPairing A hs hp).root a+(rootPairing A hs hp).root j →
      rootSign A k= -rootSign A j) :
    (rootBlock A hs hp a).transpose*rootGram A hs hp+
      rootGram A hs hp*rootBlock A hs hp a=0 := by
  ext j k
  change ((rootBlock A hs hp a).transpose*
    CFSGWeightedPermutationGram.gram (negativePerm A hs hp) (rootSign A)+
    CFSGWeightedPermutationGram.gram (negativePerm A hs hp) (rootSign A)*
      rootBlock A hs hp a) j k=0
  rw [Matrix.add_apply,CFSGWeightedPermutationGram.transpose_mul_gram,
    CFSGWeightedPermutationGram.gram_mul]
  change rootBlock A hs hp a (negativeIndex A hs hp k) j*
      rootSign A (negativeIndex A hs hp k)+
    rootSign A j*rootBlock A hs hp a (negativeIndex A hs hp j) k=0
  have he : (rootPairing A hs hp).root (negativeIndex A hs hp k)=
      (rootPairing A hs hp).root a+(rootPairing A hs hp).root j ↔
    (rootPairing A hs hp).root (negativeIndex A hs hp j)=
      (rootPairing A hs hp).root a+(rootPairing A hs hp).root k := by
    rw [root_negativeIndex,root_negativeIndex]
    exact ⟨flip_sum _ _ _,flip_sum _ _ _⟩
  unfold rootBlock
  by_cases h : (rootPairing A hs hp).root (negativeIndex A hs hp k)=
      (rootPairing A hs hp).root a+(rootPairing A hs hp).root j
  · rw [if_pos h,if_pos (he.mp h),one_mul,mul_one]
    rw [hshift j (negativeIndex A hs hp k) h]
    ring
  · rw [if_neg h,if_neg (fun h'=>h (he.mpr h')),zero_mul,mul_zero,add_zero]

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckRootGram
