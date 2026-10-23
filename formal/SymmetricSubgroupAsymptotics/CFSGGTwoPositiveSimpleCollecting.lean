import SymmetricSubgroupAsymptotics.CFSGGTwoPositiveActionCoordinates

/-! Literal two-simple-root collecting in the six checked positive Weyl
normalizations. The proof compares staged sparse actions on an arbitrary
vector and checks eight ring identities. It works over every field,
including characteristic three, with no root-group recognition premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGGTwoPositiveSimpleCollecting
open CFSGGTwoSerreMatrices CFSGGTwoPositiveDirections
open CFSGGTwoPositiveRootMatrices CFSGGTwoPositiveWordActions
open CFSGGTwoPositiveActionCoordinates
variable (R : Type*) [CommRing R]

theorem polynomial_simple_collecting (a b : R) :
    polynomialRoot R 1 b * polynomialRoot R 0 a=
      polynomialRoot R 0 a * polynomialRoot R 1 b *
        polynomialRoot R 2 (-a*b) * polynomialRoot R 3 (-a^2*b) *
          polynomialRoot R 4 (-a^3*b) * polynomialRoot R 5 (a^3*b^2) := by
  apply Matrix.mulVec_injective
  funext v
  simp only [←Matrix.mulVec_mulVec,polynomialRoot_apply,
    positiveAction_0,positiveAction_1,positiveAction_2,positiveAction_3,positiveAction_4,positiveAction_5]
  funext x
  rcases x with i|i <;> fin_cases i
  · change (action1 R b (action0 R a v)) (pos 0)=(action0 R a (action1 R b (action2 R (-a*b) (action3 R (-a^2*b) (action4 R (-a^3*b) (action5 R (a^3*b^2) v)))))) (pos 0)
    simp only [action0_pos0,action1_pos0,action1_pos1,action2_pos0,action2_pos1,action2_pos2,action3_neg1,action3_neg3,action3_pos0,action3_pos1,action3_pos2,action3_pos3,action4_neg0,action4_neg1,action4_neg2,action4_neg3,action4_pos0,action4_pos1,action4_pos2,action4_pos3,action5_neg0,action5_neg1,action5_neg2,action5_neg3,action5_pos0,action5_pos1,action5_pos2,action5_pos3] <;> ring
  · change (action1 R b (action0 R a v)) (pos 1)=(action0 R a (action1 R b (action2 R (-a*b) (action3 R (-a^2*b) (action4 R (-a^3*b) (action5 R (a^3*b^2) v)))))) (pos 1)
    simp only [action0_pos1,action0_pos2,action1_pos1,action2_pos1,action2_pos2,action3_neg1,action3_neg3,action3_pos1,action3_pos2,action3_pos3,action4_neg0,action4_neg1,action4_neg2,action4_neg3,action4_pos1,action4_pos2,action4_pos3,action5_neg0,action5_neg1,action5_neg2,action5_neg3,action5_pos1,action5_pos2,action5_pos3] <;> ring
  · change (action1 R b (action0 R a v)) (pos 2)=(action0 R a (action1 R b (action2 R (-a*b) (action3 R (-a^2*b) (action4 R (-a^3*b) (action5 R (a^3*b^2) v)))))) (pos 2)
    simp only [action0_pos2,action1_neg2,action1_neg3,action1_pos2,action1_pos3,action2_neg1,action2_neg2,action2_neg3,action2_pos2,action2_pos3,action3_neg0,action3_neg1,action3_neg2,action3_neg3,action3_pos2,action3_pos3,action4_neg0,action4_neg1,action4_neg2,action4_neg3,action4_pos2,action4_pos3,action5_neg0,action5_neg1,action5_neg2,action5_neg3,action5_pos2,action5_pos3] <;> ring
  · change (action1 R b (action0 R a v)) (pos 3)=(action0 R a (action1 R b (action2 R (-a*b) (action3 R (-a^2*b) (action4 R (-a^3*b) (action5 R (a^3*b^2) v)))))) (pos 3)
    simp only [action0_pos3,action1_neg2,action1_pos3,action2_neg1,action2_neg2,action2_pos3,action3_neg0,action3_neg1,action3_neg2,action3_pos3,action4_neg0,action4_neg1,action4_neg2,action4_pos3,action5_neg0,action5_neg1,action5_neg2,action5_pos3] <;> ring
  · change (action1 R b (action0 R a v)) (neg 0)=(action0 R a (action1 R b (action2 R (-a*b) (action3 R (-a^2*b) (action4 R (-a^3*b) (action5 R (a^3*b^2) v)))))) (neg 0)
    simp only [action0_neg0,action1_neg0,action2_neg0,action3_neg0,action4_neg0,action5_neg0] <;> ring
  · change (action1 R b (action0 R a v)) (neg 1)=(action0 R a (action1 R b (action2 R (-a*b) (action3 R (-a^2*b) (action4 R (-a^3*b) (action5 R (a^3*b^2) v)))))) (neg 1)
    simp only [action0_neg1,action1_neg0,action1_neg1,action2_neg0,action2_neg1,action3_neg0,action3_neg1,action4_neg0,action4_neg1,action5_neg0,action5_neg1] <;> ring
  · change (action1 R b (action0 R a v)) (neg 2)=(action0 R a (action1 R b (action2 R (-a*b) (action3 R (-a^2*b) (action4 R (-a^3*b) (action5 R (a^3*b^2) v)))))) (neg 2)
    simp only [action0_neg1,action0_neg2,action1_neg2,action2_neg1,action2_neg2,action3_neg0,action3_neg1,action3_neg2,action4_neg0,action4_neg1,action4_neg2,action5_neg0,action5_neg1,action5_neg2] <;> ring
  · change (action1 R b (action0 R a v)) (neg 3)=(action0 R a (action1 R b (action2 R (-a*b) (action3 R (-a^2*b) (action4 R (-a^3*b) (action5 R (a^3*b^2) v)))))) (neg 3)
    simp only [action0_neg3,action1_neg2,action1_neg3,action2_neg1,action2_neg2,action2_neg3,action3_neg0,action3_neg1,action3_neg2,action3_neg3,action4_neg0,action4_neg1,action4_neg2,action4_neg3,action5_neg0,action5_neg1,action5_neg2,action5_neg3] <;> ring

theorem simple_collecting (K : Type) [Field K] (a b : K) :
    positiveRoot K 1 b * positiveRoot K 0 a=
      positiveRoot K 0 a * positiveRoot K 1 b *
        positiveRoot K 2 (-a*b) * positiveRoot K 3 (-a^2*b) *
          positiveRoot K 4 (-a^3*b) * positiveRoot K 5 (a^3*b^2) := by
  apply Units.ext
  simp only [Units.val_mul,positiveRoot_val]
  exact polynomial_simple_collecting K a b

end SymmetricSubgroupAsymptotics.CFSGGTwoPositiveSimpleCollecting
