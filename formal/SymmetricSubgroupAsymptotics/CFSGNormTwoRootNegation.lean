import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckColumns

/-! Actual lattice root negation and its compatibility with reflections. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoRootNegation
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoGeckColumns
variable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)

theorem root_negative (i : Roots A) :
    (rootPairing A hs hp).root (negativeIndex A hs hp i)= -(rootPairing A hs hp).root i := by
  classical
  rw [negativeIndex,RootPairing.root_reflectionPerm,RootPairing.reflection_apply_self]

theorem negative_negative (i : Roots A) : negativeIndex A hs hp (negativeIndex A hs hp i)=i := by
  classical
  apply (rootPairing A hs hp).root.injective
  rw [root_negative,root_negative,neg_neg]

theorem reflection_negative (i j : Roots A) :
    (rootPairing A hs hp).reflectionPerm i (negativeIndex A hs hp j)=
      negativeIndex A hs hp ((rootPairing A hs hp).reflectionPerm i j) := by
  classical
  apply (rootPairing A hs hp).root.injective
  rw [RootPairing.root_reflectionPerm,root_negative,map_neg,root_negative,RootPairing.root_reflectionPerm]

end SymmetricSubgroupAsymptotics.CFSGNormTwoRootNegation
