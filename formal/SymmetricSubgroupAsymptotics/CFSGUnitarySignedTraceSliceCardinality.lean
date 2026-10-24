import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCentralParameters
import SymmetricSubgroupAsymptotics.AdditiveNonzeroOrbitIndex

/-! One signed Hermitian norm slice with nonzero first coordinate.
The last coordinate is an actual affine trace fibre of cardinal q;
the middle function need only have the actual signed-reality property. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGUnitarySignedTraceSliceCardinality
open CFSGTwistedAUnitaryCoordinates CFSGTwistedAUnitaryNaturalRadical
open CFSGTwistedAUnitaryParameters CFSGSerreOrdinaryTwists CFSGTwistedANaturalMatrices

def traceSlice (q : CFSG.PrimePower) (s : ℕ) {W : Type*}
    (Q : W → q.Extension 2) (c : q.Extension 2) : Set ((q.Extension 2 × W) × q.Extension 2) :=
  {v | v.1.1 ≠ 0 ∧ definingFieldAutomorphism q 2 v.1.1 * v.2 +
    parity q s * definingFieldAutomorphism q 2 v.2 * v.1.1 + Q v.1.2 = c}

theorem traceSlice_point_mem (q : CFSG.PrimePower) (s : ℕ) {W : Type*}
    (Q : W → q.Extension 2) (c : q.Extension 2) (a : W → q.Extension 2)
    (ha : ∀ w, definingFieldAutomorphism q 2 (a w) + parity q s * a w =
      parity q s * (c - Q w))
    (x : {x : q.Extension 2 // x ≠ 0}) (w : W) (z : centralParameters q s) :
    ((x.val, w), (a w + z.val) / definingFieldAutomorphism q 2 x.val) ∈ traceSlice q s Q c := by
  refine ⟨x.property, ?_⟩
  have heps : parity q s * parity q s = 1 := by
    rcases neg_one_pow_eq_or (q.Extension 2) s with h | h <;>
      change ((-1 : q.Extension 2) ^ s) * ((-1 : q.Extension 2) ^ s) = 1 <;> rw [h] <;> ring
  have hσx : definingFieldAutomorphism q 2 x.val ≠ 0 := (map_ne_zero _).mpr x.property
  have hfirst : definingFieldAutomorphism q 2 x.val *
      ((a w + z.val) / definingFieldAutomorphism q 2 x.val) = a w + z.val := by
    rw [mul_comm]
    exact div_mul_cancel₀ _ hσx
  have hsecond : definingFieldAutomorphism q 2
      ((a w + z.val) / definingFieldAutomorphism q 2 x.val) * x.val =
        definingFieldAutomorphism q 2 (a w) + definingFieldAutomorphism q 2 z.val := by
    have hσσ : definingFieldAutomorphism q 2 (definingFieldAutomorphism q 2 x.val) = x.val :=
      extension_two_pow_twice q x.val
    rw [map_div₀, map_add, hσσ, div_mul_cancel₀ _ x.property]
  have hz : parity q s * definingFieldAutomorphism q 2 z.val = -z.val := by
    rw [centralParameter_sigma q s z.val z.property]
    calc
      _ = -(parity q s * parity q s) * z.val := by ring
      _ = _ := by rw [heps]; ring
  have hab : a w + parity q s * definingFieldAutomorphism q 2 (a w) = c - Q w := by
    calc
      _ = parity q s * (definingFieldAutomorphism q 2 (a w) + parity q s * a w) := by
        rw [mul_add, ← mul_assoc, heps, one_mul]
        ring
      _ = parity q s * (parity q s * (c - Q w)) := congrArg (fun b => parity q s * b) (ha w)
      _ = _ := by rw [← mul_assoc, heps, one_mul]
  change definingFieldAutomorphism q 2 x.val *
      ((a w + z.val) / definingFieldAutomorphism q 2 x.val) +
    parity q s * definingFieldAutomorphism q 2
      ((a w + z.val) / definingFieldAutomorphism q 2 x.val) * x.val + Q w = c
  rw [hfirst, mul_assoc, hsecond, mul_add, hz]
  calc
    _ = (a w + parity q s * definingFieldAutomorphism q 2 (a w)) + Q w := by ring
    _ = c := by rw [hab]; ring

theorem card_traceSlice_lower (q : CFSG.PrimePower) (s : ℕ) (W : Type*) [Finite W]
    (Q : W → q.Extension 2)
    (hQ : ∀ w, definingFieldAutomorphism q 2 (Q w) = parity q s * Q w)
    (c : q.Extension 2) (hc : definingFieldAutomorphism q 2 c = parity q s * c) :
    (q.order ^ 2 - 1) * Nat.card W * q.order ≤ Nat.card (traceSlice q s Q c) := by
  have hε : definingFieldAutomorphism q 2 (parity q s) = parity q s := by
    change definingFieldAutomorphism q 2 ((-1 : q.Extension 2) ^ s) = _
    simp only [map_pow, map_neg, map_one]
    rfl
  have htarget (w : W) :
      definingFieldAutomorphism q 2 (parity q s * (c - Q w)) =
        parity q s * (parity q s * (c - Q w)) := by
    rw [map_mul, hε, map_sub, hc, hQ]
    ring
  let a : W → q.Extension 2 := fun w => Classical.choose
    (exists_signedTrace_eq q (parity q s) _ (neg_one_pow_eq_or _ s) (htarget w))
  have ha (w : W) : definingFieldAutomorphism q 2 (a w) + parity q s * a w =
      parity q s * (c - Q w) := Classical.choose_spec
        (exists_signedTrace_eq q (parity q s) _ (neg_one_pow_eq_or _ s) (htarget w))
  let f : (({x : q.Extension 2 // x ≠ 0} × W) × centralParameters q s) →
      traceSlice q s Q c := fun v =>
    ⟨((v.1.1.val, v.1.2), (a v.1.2 + v.2.val) / definingFieldAutomorphism q 2 v.1.1.val),
      traceSlice_point_mem q s Q c a ha v.1.1 v.1.2 v.2⟩
  have hf : Function.Injective f := by
    rintro ⟨⟨x, w⟩, z⟩ ⟨⟨x', w'⟩, z'⟩ he
    have hxx : x = x' := Subtype.ext
      (congrArg (fun v : traceSlice q s Q c => v.val.1.1) he)
    have hww : w = w' := congrArg (fun v : traceSlice q s Q c => v.val.1.2) he
    subst x'
    subst w'
    have hy : (a w + z.val) / definingFieldAutomorphism q 2 x.val =
        (a w + z'.val) / definingFieldAutomorphism q 2 x.val :=
      congrArg (fun v : traceSlice q s Q c => v.val.2) he
    have ht := congrArg (fun b : q.Extension 2 => b * definingFieldAutomorphism q 2 x.val) hy
    dsimp only at ht
    rw [div_mul_cancel₀ _ ((map_ne_zero _).mpr x.property),
      div_mul_cancel₀ _ ((map_ne_zero _).mpr x.property)] at ht
    have hzz : z = z' := Subtype.ext (add_left_cancel ht)
    subst z'
    rfl
  calc
    _ = Nat.card (({x : q.Extension 2 // x ≠ 0} × W) × centralParameters q s) := by
      rw [Nat.card_prod, Nat.card_prod, AdditiveNonzeroOrbitIndex.nonzero_card,
        CFSGTwistedANaturalMatrices.extension_two_card, centralParameters_card]
    _ ≤ _ := Nat.card_le_card_of_injective f hf

end SymmetricSubgroupAsymptotics.CFSGUnitarySignedTraceSliceCardinality
