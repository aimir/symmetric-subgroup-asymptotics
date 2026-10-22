import SymmetricSubgroupAsymptotics.CFSGNormTwoRootPairing
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Actual simply-laced pairing bounds in a norm-two positive-definite lattice.
These constrain the later Geck root strings without a finite-type assumption. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoPairingBounds
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
variable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)

include hp in
theorem norm_eq_zero_iff (x : n→ℤ) : integerPairing A x x=0 ↔ x=0 := by
  constructor
  · intro hx
    by_contra hne
    have hcx : castVector x≠0 := by
      intro h
      apply hne
      apply castVector_injective
      simpa [castVector] using h
    have hpos : (0:ℚ)<(integerPairing A x x:ℚ) := by
      rw [←cast_pairing]
      simpa only [rationalPairing,Matrix.toBilin'_apply',star_trivial] using
        hp.dotProduct_mulVec_pos hcx
    rw [hx] at hpos
    norm_num at hpos
  · intro hx
    simp [hx]

include hp in
theorem norm_nonneg (x : n→ℤ) : 0 ≤ integerPairing A x x := by
  by_cases hx : x=0
  · simp [hx]
  have hcx : castVector x≠0 := by
    intro h
    apply hx
    apply castVector_injective
    simpa [castVector] using h
  have hpos : (0:ℚ)<(integerPairing A x x:ℚ) := by
    rw [←cast_pairing]
    simpa only [rationalPairing,Matrix.toBilin'_apply',star_trivial] using
      hp.dotProduct_mulVec_pos hcx
  exact le_of_lt (by exact_mod_cast hpos)

include hs in
theorem norm_add (x y : n→ℤ) : integerPairing A (x+y) (x+y)=
    integerPairing A x x+integerPairing A y y+2*integerPairing A x y := by
  simp only [map_add,LinearMap.add_apply,integer_symmetric A hs y x]
  ring

include hs in
theorem norm_sub (x y : n→ℤ) : integerPairing A (x-y) (x-y)=
    integerPairing A x x+integerPairing A y y-2*integerPairing A x y := by
  simp only [map_sub,LinearMap.sub_apply,integer_symmetric A hs y x]
  ring

include hs hp in
theorem root_pairing_bounds (i j : Roots A) :
    -2 ≤ integerPairing A i.val j.val ∧ integerPairing A i.val j.val ≤ 2 := by
  have hplus := norm_nonneg A hp (i.val+j.val)
  have hminus := norm_nonneg A hp (i.val-j.val)
  rw [norm_add A hs,i.property,j.property] at hplus
  rw [norm_sub A hs,i.property,j.property] at hminus
  omega

include hs hp in
theorem root_pairing_eq_two_iff (i j : Roots A) :
    integerPairing A i.val j.val=2 ↔ i=j := by
  constructor
  · intro h
    apply Subtype.ext
    apply sub_eq_zero.mp
    apply (norm_eq_zero_iff A hp _).mp
    rw [norm_sub A hs,i.property,j.property,h]
    norm_num
  · intro h
    subst j
    exact i.property

include hs hp in
theorem root_pairing_eq_neg_two_iff (i j : Roots A) :
    integerPairing A i.val j.val= -2 ↔ i.val= -j.val := by
  constructor
  · intro h
    apply eq_neg_iff_add_eq_zero.mpr
    apply (norm_eq_zero_iff A hp _).mp
    rw [norm_add A hs,i.property,j.property,h]
    norm_num
  · intro h
    rw [h,map_neg,LinearMap.neg_apply,j.property]

include hs hp in
theorem root_pairing_interior (i j : Roots A) (hij : i≠j) (hopp : i.val≠ -j.val) :
    integerPairing A i.val j.val= -1 ∨ integerPairing A i.val j.val=0 ∨
      integerPairing A i.val j.val=1 := by
  have hb := root_pairing_bounds A hs hp i j
  have htwo : integerPairing A i.val j.val≠2 :=
    fun h=>hij ((root_pairing_eq_two_iff A hs hp i j).mp h)
  have hneg : integerPairing A i.val j.val≠ -2 :=
    fun h=>hopp ((root_pairing_eq_neg_two_iff A hs hp i j).mp h)
  omega

end SymmetricSubgroupAsymptotics.CFSGNormTwoPairingBounds
