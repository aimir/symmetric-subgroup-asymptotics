import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckLatticeDegree

/-! The actual rational negative Geck operator lowers the SAME original
integer lattice by its simple root. No division or coefficient-field
separation is involved. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckNegativeLatticeDegree
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoGeckLatticeDegree CFSGGradedMatrixSupport CFSGNormTwoGeckColumns
variable {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    (b : (rootPairing A hs hp).Base)

theorem rational_F_lattice_support (i : b.support) :
    Supported (latticeWeight A hs hp b) (fun w=>w-(i:Roots A).val)
      (RootPairing.GeckConstruction.f i) := by
  intro j k hne
  rcases j with j|j <;> rcases k with k|k
  · rfl
  · simp only [RootPairing.GeckConstruction.f,Matrix.fromBlocks_apply₁₂,Matrix.of_apply]
    split_ifs with h
    · obtain ⟨hji,hki⟩ := h
      subst j
      subst k
      exfalso
      apply hne
      change 0=(i:Roots A).val-(i:Roots A).val
      exact (sub_self _).symm
    · rfl
  · simp only [RootPairing.GeckConstruction.f,Matrix.fromBlocks_apply₂₁,Matrix.of_apply]
    split_ifs with h
    · subst j
      exfalso
      apply hne
      change (negativeIndex A hs hp i).val=0-(i:Roots A).val
      rw [CFSGNormTwoGeckColumns.negative_val,zero_sub]
    · rfl
  · simp only [RootPairing.GeckConstruction.f,Matrix.fromBlocks_apply₂₂,Matrix.of_apply]
    split_ifs with h
    · exfalso
      apply hne
      change j.val=k.val-(i:Roots A).val
      ext t
      have ht := congrFun h t
      change (j.val t:ℚ)=(k.val t:ℚ)-((i:Roots A).val t:ℚ) at ht
      exact_mod_cast ht
    · rfl

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckNegativeLatticeDegree
