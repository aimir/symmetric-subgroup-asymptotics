import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckColumns

/-! The actual root-to-root Geck entries reduce to zero or one in the
norm-two lattice, by the proved root-string coefficient calculation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckNormalizedEntries
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoRootStrings
open CFSGNormTwoGeckColumns
variable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    (b : (rootPairing A hs hp).Base)

theorem E_inl_inl (i j k : b.support) :
    RootPairing.GeckConstruction.e i (Sum.inl j) (Sum.inl k)=0 := rfl

theorem E_inl_inr (i j : b.support) (k : Roots A) :
    RootPairing.GeckConstruction.e i (Sum.inl j) (Sum.inr k)=
      if j=i ∧ k=negativeIndex A hs hp i then 1 else 0 := by
  classical
  simp only [RootPairing.GeckConstruction.e,Matrix.fromBlocks_apply₁₂,Matrix.of_apply,
    RootPairing.indexNeg_neg,negativeIndex] <;> split_ifs <;> rfl

theorem E_inr_inl (i k : b.support) (j : Roots A) :
    RootPairing.GeckConstruction.e i (Sum.inr j) (Sum.inl k)=
      if j=(i:Roots A) then ((|b.cartanMatrix i k|:ℤ):ℚ) else 0 := by
  classical
  simp only [RootPairing.GeckConstruction.e,Matrix.fromBlocks_apply₂₁,Matrix.of_apply] <;>
    split_ifs <;> rfl

theorem E_inr_inr (i : b.support) (j k : Roots A) :
    RootPairing.GeckConstruction.e i (Sum.inr j) (Sum.inr k)=
      if (rootPairing A hs hp).root j=(rootPairing A hs hp).root i+
        (rootPairing A hs hp).root k then 1 else 0 := by
  classical
  simp only [RootPairing.GeckConstruction.e,Matrix.fromBlocks_apply₂₂,Matrix.of_apply]
  split_ifs with h
  · rw [chainBotCoeff_of_root_add A hs hp h]
    norm_num
  · rfl

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckNormalizedEntries
