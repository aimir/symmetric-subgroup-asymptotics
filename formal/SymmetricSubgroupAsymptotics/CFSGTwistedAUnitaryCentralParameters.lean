import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCentralDerived
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryRadicalFixedSpace
import SymmetricSubgroupAsymptotics.CFSGTwistedA2FixedField

/-! The actual signed central parameter line has q elements. Dividing
by a genuine nonzero central parameter gives the ACTUAL Frobenius-fixed
subfield. This is valid in both characteristics and for either parity. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGSerreOrdinaryTwists CFSGTwistedAUnitaryNaturalRadical
open CFSGTwistedA2FixedField

def centralTraceHom (q : CFSG.PrimePower) (s : ℕ) : q.Extension 2 →+ q.Extension 2 where
  toFun c := definingFieldAutomorphism q 2 c + parity q s * c
  map_zero' := by
    change definingFieldAutomorphism q 2 0 + parity q s * 0 = 0
    rw [map_zero, mul_zero, add_zero]
  map_add' x y := by simp only [map_add, mul_add]; abel

def centralParameters (q : CFSG.PrimePower) (s : ℕ) : AddSubgroup (q.Extension 2) :=
  (centralTraceHom q s).ker

theorem mem_centralParameters (q : CFSG.PrimePower) (s : ℕ) (c : q.Extension 2) :
    c ∈ centralParameters q s ↔ definingFieldAutomorphism q 2 c + parity q s * c = 0 :=
  Iff.rfl

theorem centralParameters_condition (q : CFSG.PrimePower) (s : ℕ) (c : q.Extension 2)
    (hc : c ∈ centralParameters q s) : Condition q s 0 c :=
  (centralCondition_iff q s c).mpr hc

theorem centralParameter_sigma (q : CFSG.PrimePower) (s : ℕ) (c : q.Extension 2)
    (hc : c ∈ centralParameters q s) :
    definingFieldAutomorphism q 2 c = -(parity q s * c) :=
  eq_neg_of_add_eq_zero_left hc

theorem centralParameter_mul_fixed (q : CFSG.PrimePower) (s : ℕ)
    (t : q.Extension 2) (ht : t ∈ centralParameters q s) (a : fixedField q) :
    t * a.val ∈ centralParameters q s := by
  change definingFieldAutomorphism q 2 (t * a.val) + parity q s * (t * a.val) = 0
  have ha : definingFieldAutomorphism q 2 a.val = a.val := a.property
  rw [map_mul, ha, centralParameter_sigma q s t ht]
  ring

theorem centralParameter_div_fixed (q : CFSG.PrimePower) (s : ℕ)
    (t : q.Extension 2) (ht0 : t ≠ 0) (ht : t ∈ centralParameters q s)
    (c : centralParameters q s) : t⁻¹ * c.val ∈ fixedField q := by
  change definingFieldAutomorphism q 2 (t⁻¹ * c.val) = t⁻¹ * c.val
  have he : parity q s ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  rw [map_mul, map_inv₀, centralParameter_sigma q s t ht,
    centralParameter_sigma q s c.val c.property]
  field_simp [ht0, he]

def centralParametersEquivFixed (q : CFSG.PrimePower) (s : ℕ)
    (t : q.Extension 2) (ht0 : t ≠ 0) (ht : t ∈ centralParameters q s) :
    fixedField q ≃+ centralParameters q s where
  toFun a := ⟨t * a.val, centralParameter_mul_fixed q s t ht a⟩
  invFun c := ⟨t⁻¹ * c.val, centralParameter_div_fixed q s t ht0 ht c⟩
  left_inv a := by
    apply Subtype.ext
    change t⁻¹ * (t * a.val) = a.val
    rw [← mul_assoc, inv_mul_cancel₀ ht0, one_mul]
  right_inv c := by
    apply Subtype.ext
    change t * (t⁻¹ * c.val) = c.val
    rw [← mul_assoc, mul_inv_cancel₀ ht0, one_mul]
  map_add' a b := by
    apply Subtype.ext
    exact mul_add t a.val b.val

theorem centralParameters_card (q : CFSG.PrimePower) (s : ℕ) :
    Nat.card (centralParameters q s) = q.order := by
  obtain ⟨t, ht0, htc⟩ := exists_nonzero_central_parameter q s
  have ht : t ∈ centralParameters q s := (centralCondition_iff q s t).mp htc
  exact (Nat.card_congr (centralParametersEquivFixed q s t ht0 ht).toEquiv).symm.trans
    (fixedField_card q)

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
