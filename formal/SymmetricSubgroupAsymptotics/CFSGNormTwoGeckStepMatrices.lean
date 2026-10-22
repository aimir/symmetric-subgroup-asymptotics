import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckNormalizedEntries

/-! Both actual Geck signs are instances of one root-step matrix. This
lets the same explicit Gram calculation cover E and F. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckStepMatrices
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoGeckColumns
open CFSGNormTwoRootStrings CFSGNormTwoGeckNormalizedEntries
variable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    (b : (rootPairing A hs hp).Base)

theorem negativeIndex_involutive : Function.Involutive (negativeIndex A hs hp) := by
  intro i
  apply Subtype.ext
  rw [negative_val,negative_val,neg_neg]

theorem root_negativeIndex (i : Roots A) :
    (rootPairing A hs hp).root (negativeIndex A hs hp i)= -(rootPairing A hs hp).root i := by
  unfold negativeIndex
  rw [RootPairing.root_reflectionPerm,RootPairing.reflection_apply_self]

def rootBlock (a : Roots A) : Matrix (Roots A) (Roots A) ℚ :=
  fun j k=>if (rootPairing A hs hp).root j=
    (rootPairing A hs hp).root a+(rootPairing A hs hp).root k then 1 else 0

def stepMatrix (a : Roots A) (i : b.support) :
    Matrix (b.support⊕Roots A) (b.support⊕Roots A) ℚ :=
  Matrix.fromBlocks 0
    (fun j k=>if j=i ∧ k=negativeIndex A hs hp a then 1 else 0)
    (fun j k=>if j=a then ((|b.cartanMatrix i k|:ℤ):ℚ) else 0)
    (rootBlock A hs hp a)

theorem E_eq_step (i : b.support) :
    RootPairing.GeckConstruction.e i=stepMatrix A hs hp b i i := by
  ext (j|j) (k|k)
  · exact E_inl_inl A hs hp b i j k
  · exact E_inl_inr A hs hp b i j k
  · exact E_inr_inl A hs hp b i k j
  · exact E_inr_inr A hs hp b i j k

theorem F_eq_step (i : b.support) :
    RootPairing.GeckConstruction.f i=stepMatrix A hs hp b (negativeIndex A hs hp i) i := by
  classical
  ext (j|j) (k|k)
  · rfl
  · simp [RootPairing.GeckConstruction.f,stepMatrix,negativeIndex_involutive A hs hp i]
  · simp only [RootPairing.GeckConstruction.f,stepMatrix,Matrix.fromBlocks_apply₂₁,
      Matrix.of_apply,RootPairing.indexNeg_neg,negativeIndex] <;> split_ifs <;> rfl
  · simp only [RootPairing.GeckConstruction.f,stepMatrix,Matrix.fromBlocks_apply₂₂,
      Matrix.of_apply,rootBlock,root_negativeIndex,neg_add_eq_sub]
    split_ifs with h
    · rw [chainTopCoeff_of_root_sub A hs hp h]
      norm_num
    · rfl

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckStepMatrices
