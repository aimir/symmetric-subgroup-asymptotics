import SymmetricSubgroupAsymptotics.CFSGNormTwoRootNeighbors

/-! Coordinate and reflection identities for actual norm-two root steps.
No enumeration or named root-system identification is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoRootStepCoordinates
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
variable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)

theorem root_add_val {i j k : Roots A}
    (hk : (rootPairing A hs hp).root k=(rootPairing A hs hp).root i+(rootPairing A hs hp).root j) :
    k.val=i.val+j.val := by
  ext t
  have ht := congrFun hk t
  change (k.val t:ℚ)=(i.val t:ℚ)+(j.val t:ℚ) at ht
  exact_mod_cast ht

theorem reflection_fixed (i j : Roots A) (h : integerPairing A i.val j.val=0) :
    (rootPairing A hs hp).reflectionPerm i j=j := by
  apply (rootPairing A hs hp).root.injective
  rw [RootPairing.root_reflectionPerm,RootPairing.reflection_apply_root,pairing_cast,
    integer_symmetric A hs j.val i.val,h,Int.cast_zero,zero_smul,sub_zero]

theorem reflection_add {i j k : Roots A}
    (h : integerPairing A i.val j.val= -1)
    (hk : (rootPairing A hs hp).root k=(rootPairing A hs hp).root i+(rootPairing A hs hp).root j) :
    (rootPairing A hs hp).reflectionPerm i j=k := by
  apply (rootPairing A hs hp).root.injective
  rw [RootPairing.root_reflectionPerm,RootPairing.reflection_apply_root,pairing_cast,
    integer_symmetric A hs j.val i.val,h,Int.cast_neg,Int.cast_one,neg_one_smul,sub_neg_eq_add,hk]
  abel

theorem reflection_sub {i j k : Roots A}
    (h : integerPairing A i.val j.val=1)
    (hk : (rootPairing A hs hp).root k=(rootPairing A hs hp).root j-(rootPairing A hs hp).root i) :
    (rootPairing A hs hp).reflectionPerm i j=k := by
  apply (rootPairing A hs hp).root.injective
  rw [RootPairing.root_reflectionPerm,RootPairing.reflection_apply_root,pairing_cast,
    integer_symmetric A hs j.val i.val,h,Int.cast_one,one_smul]
  exact hk.symm

end SymmetricSubgroupAsymptotics.CFSGNormTwoRootStepCoordinates
