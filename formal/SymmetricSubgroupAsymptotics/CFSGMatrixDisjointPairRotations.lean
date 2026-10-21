import SymmetricSubgroupAsymptotics.CFSGMatrixPairRotationAction

/-! Disjoint coordinate rotations commute and their product has fourth
power one. These identities hold over every commutative ring. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGMatrixPairRotation
variable (R : Type*) [CommRing R] {I : Type*} [Fintype I] [DecidableEq I]

theorem disjoint_rotation_commute (a b c d : I)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    Commute (rotation R a b) (rotation R c d) := by
  change rotation R a b * rotation R c d = rotation R c d * rotation R a b
  simp [rotation, sub_mul, mul_sub, add_mul, mul_add,
    hac, had, hbc, hbd, Ne.symm hac, Ne.symm had, Ne.symm hbc, Ne.symm hbd] <;> abel

theorem disjoint_rotation_four (a b c d : I) (hab : a ≠ b) (hcd : c ≠ d)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    (rotation R a b * rotation R c d) ^ 4 = 1 := by
  rw [(disjoint_rotation_commute R a b c d hac had hbc hbd).mul_pow,
    rotation_four R a b hab, rotation_four R c d hcd, one_mul]

end SymmetricSubgroupAsymptotics.CFSGMatrixPairRotation
