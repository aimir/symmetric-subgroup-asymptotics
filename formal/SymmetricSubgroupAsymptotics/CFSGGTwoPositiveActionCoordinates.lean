import SymmetricSubgroupAsymptotics.CFSGGTwoPositiveWordActions

/-! Applied-coordinate interfaces for the six checked sparse actions.
Every identity is definitional. Rewriting applied coordinates rather than
unfolding whole vector functions keeps collecting proofs small. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoPositiveActionCoordinates
open CFSGGTwoSerreMatrices CFSGGTwoPositiveWordActions
variable (R : Type*) [CommRing R]

theorem action0_pos0 (t : R) (v : Index → R) :
    action0 R t v (pos 0)=v (pos 0)+t*v (pos 1) := rfl

theorem action0_pos1 (t : R) (v : Index → R) :
    action0 R t v (pos 1)=v (pos 1) := rfl

theorem action0_pos2 (t : R) (v : Index → R) :
    action0 R t v (pos 2)=v (pos 2)+t*(v (pos 3)+v (neg 3))-t^2*v (neg 2) := rfl

theorem action0_pos3 (t : R) (v : Index → R) :
    action0 R t v (pos 3)=v (pos 3)-t*v (neg 2) := rfl

theorem action0_neg0 (t : R) (v : Index → R) :
    action0 R t v (neg 0)=v (neg 0) := rfl

theorem action0_neg1 (t : R) (v : Index → R) :
    action0 R t v (neg 1)=v (neg 1)-t*v (neg 0) := rfl

theorem action0_neg2 (t : R) (v : Index → R) :
    action0 R t v (neg 2)=v (neg 2) := rfl

theorem action0_neg3 (t : R) (v : Index → R) :
    action0 R t v (neg 3)=v (neg 3)-t*v (neg 2) := rfl

theorem action1_pos0 (t : R) (v : Index → R) :
    action1 R t v (pos 0)=v (pos 0) := rfl

theorem action1_pos1 (t : R) (v : Index → R) :
    action1 R t v (pos 1)=v (pos 1)+t*v (pos 2) := rfl

theorem action1_pos2 (t : R) (v : Index → R) :
    action1 R t v (pos 2)=v (pos 2) := rfl

theorem action1_pos3 (t : R) (v : Index → R) :
    action1 R t v (pos 3)=v (pos 3) := rfl

theorem action1_neg0 (t : R) (v : Index → R) :
    action1 R t v (neg 0)=v (neg 0) := rfl

theorem action1_neg1 (t : R) (v : Index → R) :
    action1 R t v (neg 1)=v (neg 1) := rfl

theorem action1_neg2 (t : R) (v : Index → R) :
    action1 R t v (neg 2)=v (neg 2)-t*v (neg 1) := rfl

theorem action1_neg3 (t : R) (v : Index → R) :
    action1 R t v (neg 3)=v (neg 3) := rfl

theorem action2_pos0 (t : R) (v : Index → R) :
    action2 R t v (pos 0)=v (pos 0)+t*v (pos 2) := rfl

theorem action2_pos1 (t : R) (v : Index → R) :
    action2 R t v (pos 1)=v (pos 1)-t*(v (pos 3)+v (neg 3))-t^2*v (neg 1) := rfl

theorem action2_pos2 (t : R) (v : Index → R) :
    action2 R t v (pos 2)=v (pos 2) := rfl

theorem action2_pos3 (t : R) (v : Index → R) :
    action2 R t v (pos 3)=v (pos 3)+t*v (neg 1) := rfl

theorem action2_neg0 (t : R) (v : Index → R) :
    action2 R t v (neg 0)=v (neg 0) := rfl

theorem action2_neg1 (t : R) (v : Index → R) :
    action2 R t v (neg 1)=v (neg 1) := rfl

theorem action2_neg2 (t : R) (v : Index → R) :
    action2 R t v (neg 2)=v (neg 2)-t*v (neg 0) := rfl

theorem action2_neg3 (t : R) (v : Index → R) :
    action2 R t v (neg 3)=v (neg 3)+t*v (neg 1) := rfl

theorem action3_pos0 (t : R) (v : Index → R) :
    action3 R t v (pos 0)=v (pos 0)+t*(v (pos 3)+v (neg 3))-t^2*v (neg 0) := rfl

theorem action3_pos1 (t : R) (v : Index → R) :
    action3 R t v (pos 1)=v (pos 1)+t*v (neg 2) := rfl

theorem action3_pos2 (t : R) (v : Index → R) :
    action3 R t v (pos 2)=v (pos 2)-t*v (neg 1) := rfl

theorem action3_pos3 (t : R) (v : Index → R) :
    action3 R t v (pos 3)=v (pos 3)-t*v (neg 0) := rfl

theorem action3_neg0 (t : R) (v : Index → R) :
    action3 R t v (neg 0)=v (neg 0) := rfl

theorem action3_neg1 (t : R) (v : Index → R) :
    action3 R t v (neg 1)=v (neg 1) := rfl

theorem action3_neg2 (t : R) (v : Index → R) :
    action3 R t v (neg 2)=v (neg 2) := rfl

theorem action3_neg3 (t : R) (v : Index → R) :
    action3 R t v (neg 3)=v (neg 3)-t*v (neg 0) := rfl

theorem action4_pos0 (t : R) (v : Index → R) :
    action4 R t v (pos 0)=v (pos 0)-t*v (neg 2) := rfl

theorem action4_pos1 (t : R) (v : Index → R) :
    action4 R t v (pos 1)=v (pos 1) := rfl

theorem action4_pos2 (t : R) (v : Index → R) :
    action4 R t v (pos 2)=v (pos 2)+t*v (neg 0) := rfl

theorem action4_pos3 (t : R) (v : Index → R) :
    action4 R t v (pos 3)=v (pos 3) := rfl

theorem action4_neg0 (t : R) (v : Index → R) :
    action4 R t v (neg 0)=v (neg 0) := rfl

theorem action4_neg1 (t : R) (v : Index → R) :
    action4 R t v (neg 1)=v (neg 1) := rfl

theorem action4_neg2 (t : R) (v : Index → R) :
    action4 R t v (neg 2)=v (neg 2) := rfl

theorem action4_neg3 (t : R) (v : Index → R) :
    action4 R t v (neg 3)=v (neg 3) := rfl

theorem action5_pos0 (t : R) (v : Index → R) :
    action5 R t v (pos 0)=v (pos 0)+t*v (neg 1) := rfl

theorem action5_pos1 (t : R) (v : Index → R) :
    action5 R t v (pos 1)=v (pos 1)-t*v (neg 0) := rfl

theorem action5_pos2 (t : R) (v : Index → R) :
    action5 R t v (pos 2)=v (pos 2) := rfl

theorem action5_pos3 (t : R) (v : Index → R) :
    action5 R t v (pos 3)=v (pos 3) := rfl

theorem action5_neg0 (t : R) (v : Index → R) :
    action5 R t v (neg 0)=v (neg 0) := rfl

theorem action5_neg1 (t : R) (v : Index → R) :
    action5 R t v (neg 1)=v (neg 1) := rfl

theorem action5_neg2 (t : R) (v : Index → R) :
    action5 R t v (neg 2)=v (neg 2) := rfl

theorem action5_neg3 (t : R) (v : Index → R) :
    action5 R t v (neg 3)=v (neg 3) := rfl

end SymmetricSubgroupAsymptotics.CFSGGTwoPositiveActionCoordinates
