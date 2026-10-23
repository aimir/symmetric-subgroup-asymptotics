import SymmetricSubgroupAsymptotics.CFSGNormTwoPairingBounds

/-! Four-step norm gaps in three mutually orthogonal actual norm-two
roots. The coefficients are nonnegative integers with sum four; no
finite root census or characteristic restriction is used. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoOrthogonalTripleNorms
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoPairingBounds

private theorem integer_square_ge_self (t : ℤ) : t≤t^2 := by
  by_cases ht : t≤0
  · nlinarith [sq_nonneg t]
  · have hmul := mul_nonneg (show 0≤t by omega) (show 0≤t-1 by omega)
    nlinarith

private theorem three_squares_ge_six (x y z : ℤ) (hx : 0≤x) (hy : 0≤y) (hz : 0≤z)
    (hsum : x+y+z=4) : 6≤x^2+y^2+z^2 := by
  have hstep (t : ℤ) (ht : 2≤t) : 2≤t^2-t := by
    have hmul := mul_nonneg (show 0≤t-2 by omega) (show 0≤t+1 by omega)
    nlinarith
  have hsqx := integer_square_ge_self x
  have hsqy := integer_square_ge_self y
  have hsqz := integer_square_ge_self z
  have hlarge : 2≤x ∨ 2≤y ∨ 2≤z := by omega
  rcases hlarge with h|h|h
  · nlinarith [hstep x h]
  · nlinarith [hstep y h]
  · nlinarith [hstep z h]

private theorem weighted_pairings_ge_six (x y z p q s : ℤ)
    (hx : 0≤x) (hy : 0≤y) (hz : 0≤z) (hsum : x+y+z=4)
    (hp : -2≤p) (hq : -2≤q) (hs : -2≤s)
    (hpzero : p= -2→q=0 ∧ s=0) (hqzero : q= -2→p=0 ∧ s=0)
    (hszero : s= -2→p=0 ∧ q=0) :
    6≤2+2*(x^2+y^2+z^2)+2*x*p+2*y*q+2*z*s := by
  by_cases hp' : p= -2
  · obtain ⟨rfl,rfl⟩ := hpzero hp'
    rw [hp']
    nlinarith [integer_square_ge_self (x-1),integer_square_ge_self y,integer_square_ge_self z]
  by_cases hq' : q= -2
  · obtain ⟨rfl,rfl⟩ := hqzero hq'
    rw [hq']
    nlinarith [integer_square_ge_self x,integer_square_ge_self (y-1),integer_square_ge_self z]
  by_cases hs' : s= -2
  · obtain ⟨rfl,rfl⟩ := hszero hs'
    rw [hs']
    nlinarith [integer_square_ge_self x,integer_square_ge_self y,integer_square_ge_self (z-1)]
  have hxp := mul_nonneg hx (show 0≤p+1 by omega)
  have hyq := mul_nonneg hy (show 0≤q+1 by omega)
  have hzs := mul_nonneg hz (show 0≤s+1 by omega)
  nlinarith [three_squares_ge_six x y z hx hy hz hsum]

variable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)

include hs in
theorem three_orthogonal_norm (a b c : Roots A)
    (hab : integerPairing A a.val b.val=0) (hac : integerPairing A a.val c.val=0)
    (hbc : integerPairing A b.val c.val=0) (x y z : ℤ) :
    integerPairing A (x • a.val+y • b.val+z • c.val) (x • a.val+y • b.val+z • c.val)=
      2*(x^2+y^2+z^2) := by
  simp only [map_add,LinearMap.add_apply,(integerPairing A).smul_left,
    (integerPairing A).smul_right,smul_eq_mul]
  rw [a.property,b.property,c.property,hab,hac,hbc,
    integer_symmetric A hs b.val a.val,hab,integer_symmetric A hs c.val a.val,hac,
    integer_symmetric A hs c.val b.val,hbc]
  ring

include hs in
theorem root_plus_three_orthogonal_norm (k a b c : Roots A)
    (hab : integerPairing A a.val b.val=0) (hac : integerPairing A a.val c.val=0)
    (hbc : integerPairing A b.val c.val=0) (x y z : ℤ) :
    integerPairing A (k.val+(x • a.val+y • b.val+z • c.val))
      (k.val+(x • a.val+y • b.val+z • c.val))=
      2+2*(x^2+y^2+z^2)+2*x*integerPairing A k.val a.val+
        2*y*integerPairing A k.val b.val+2*z*integerPairing A k.val c.val := by
  rw [norm_add A hs,k.property,three_orthogonal_norm A hs a b c hab hac hbc x y z]
  simp only [map_add,(integerPairing A).smul_right,smul_eq_mul]
  ring

include hs in
theorem four_steps_norm_ge_twelve (a b c : Roots A)
    (hab : integerPairing A a.val b.val=0) (hac : integerPairing A a.val c.val=0)
    (hbc : integerPairing A b.val c.val=0) (x y z : ℤ)
    (hx : 0≤x) (hy : 0≤y) (hz : 0≤z) (hsum : x+y+z=4) :
    12 ≤ integerPairing A (x • a.val+y • b.val+z • c.val)
      (x • a.val+y • b.val+z • c.val) := by
  rw [three_orthogonal_norm A hs a b c hab hac hbc x y z]
  nlinarith [three_squares_ge_six x y z hx hy hz hsum]

include hs hp in
theorem root_four_steps_norm_ge_six (k a b c : Roots A)
    (hab : integerPairing A a.val b.val=0) (hac : integerPairing A a.val c.val=0)
    (hbc : integerPairing A b.val c.val=0) (x y z : ℤ)
    (hx : 0≤x) (hy : 0≤y) (hz : 0≤z) (hsum : x+y+z=4) :
    6 ≤ integerPairing A (k.val+(x • a.val+y • b.val+z • c.val))
      (k.val+(x • a.val+y • b.val+z • c.val)) := by
  rw [root_plus_three_orthogonal_norm A hs k a b c hab hac hbc x y z]
  apply weighted_pairings_ge_six x y z _ _ _ hx hy hz hsum
    (root_pairing_bounds A hs hp k a).1 (root_pairing_bounds A hs hp k b).1
    (root_pairing_bounds A hs hp k c).1
  · intro hka
    have hk := (root_pairing_eq_neg_two_iff A hs hp k a).mp hka
    constructor
    · rw [hk,map_neg,LinearMap.neg_apply,hab,neg_zero]
    · rw [hk,map_neg,LinearMap.neg_apply,hac,neg_zero]
  · intro hkb
    have hk := (root_pairing_eq_neg_two_iff A hs hp k b).mp hkb
    constructor
    · rw [hk,map_neg,LinearMap.neg_apply,integer_symmetric A hs b.val a.val,hab,neg_zero]
    · rw [hk,map_neg,LinearMap.neg_apply,hbc,neg_zero]
  · intro hkc
    have hk := (root_pairing_eq_neg_two_iff A hs hp k c).mp hkc
    constructor
    · rw [hk,map_neg,LinearMap.neg_apply,integer_symmetric A hs c.val a.val,hac,neg_zero]
    · rw [hk,map_neg,LinearMap.neg_apply,integer_symmetric A hs c.val b.val,hbc,neg_zero]

end SymmetricSubgroupAsymptotics.CFSGNormTwoOrthogonalTripleNorms
