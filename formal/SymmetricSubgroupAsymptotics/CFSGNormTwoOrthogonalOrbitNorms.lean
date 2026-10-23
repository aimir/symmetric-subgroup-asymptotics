import SymmetricSubgroupAsymptotics.CFSGNormTwoPairingBounds

/-! Actual norm gaps for three steps in two orthogonal norm-two roots.
These are lattice calculations, independent of a coefficient field or
of a folded-group recognition theorem. They will control the adjoint
cube of an orthogonal pair on the same generated Geck Lie algebra. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoOrthogonalOrbitNorms
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoPairingBounds
variable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)

theorem triple_root_norm (a : Roots A) :
    integerPairing A ((3:ℤ) • a.val) ((3:ℤ) • a.val)=18 := by
  simp only [(integerPairing A).smul_left,(integerPairing A).smul_right,
    a.property,smul_eq_mul]
  norm_num

include hs in
theorem double_orthogonal_norm (a b : Roots A)
    (hab : integerPairing A a.val b.val=0) :
    integerPairing A ((2:ℤ) • a.val+b.val) ((2:ℤ) • a.val+b.val)=10 := by
  simp only [map_add,LinearMap.add_apply,(integerPairing A).smul_left,
    (integerPairing A).smul_right,smul_eq_mul]
  rw [a.property,b.property,hab,integer_symmetric A hs b.val a.val,hab]
  norm_num

include hs hp in
theorem root_plus_triple_norm_ge_four (k a : Roots A) :
    4 ≤ integerPairing A (k.val+(3:ℤ) • a.val) (k.val+(3:ℤ) • a.val) := by
  have hnorm : integerPairing A (k.val+(3:ℤ) • a.val)
      (k.val+(3:ℤ) • a.val)=20+6*integerPairing A k.val a.val := by
    simp only [map_add,LinearMap.add_apply,(integerPairing A).smul_left,
      (integerPairing A).smul_right,smul_eq_mul]
    rw [k.property,a.property,integer_symmetric A hs a.val k.val]
    ring
  have hb := (root_pairing_bounds A hs hp k a).1
  omega

include hs hp in
theorem root_plus_double_orthogonal_norm_ge_four (k a b : Roots A)
    (hab : integerPairing A a.val b.val=0) :
    4 ≤ integerPairing A (k.val+((2:ℤ) • a.val+b.val))
      (k.val+((2:ℤ) • a.val+b.val)) := by
  have hnorm : integerPairing A (k.val+((2:ℤ) • a.val+b.val))
      (k.val+((2:ℤ) • a.val+b.val))=
      12+4*integerPairing A k.val a.val+2*integerPairing A k.val b.val := by
    simp only [map_add,LinearMap.add_apply,(integerPairing A).smul_left,
      (integerPairing A).smul_right,smul_eq_mul]
    rw [k.property,a.property,b.property,hab,integer_symmetric A hs b.val a.val,hab,
      integer_symmetric A hs a.val k.val,integer_symmetric A hs b.val k.val]
    ring
  by_cases hka : integerPairing A k.val a.val= -2
  · have hval := (root_pairing_eq_neg_two_iff A hs hp k a).mp hka
    have hkb : integerPairing A k.val b.val=0 := by
      rw [hval,map_neg,LinearMap.neg_apply,hab,neg_zero]
    rw [hnorm,hka,hkb]
    norm_num
  · have hka' := (root_pairing_bounds A hs hp k a).1
    have hkb := (root_pairing_bounds A hs hp k b).1
    omega

end SymmetricSubgroupAsymptotics.CFSGNormTwoOrthogonalOrbitNorms
