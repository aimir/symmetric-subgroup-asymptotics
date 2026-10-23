import SymmetricSubgroupAsymptotics.CFSGTrialityTripleFixedRoots
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.Data.Set.Card

/-! The actual Frobenius-fixed subfield in the literal cubic
extension has q elements. An existing finite-field embedding and the
root bound for X^q-X prove this without a named group identification. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Polynomial

namespace SymmetricSubgroupAsymptotics.CFSGTrialityFixedField
open CFSGSerreOrdinaryTwists

theorem sigma_thrice (q : CFSG.PrimePower) (a : q.Extension 3) :
    definingFieldAutomorphism q 3 (definingFieldAutomorphism q 3
      (definingFieldAutomorphism q 3 a)) = a :=
  CFSGTrialityTripleFixedRoots.extension_three_pow_thrice q a

def fixedField (q : CFSG.PrimePower) : Subfield (q.Extension 3) :=
  (definingFieldAutomorphism q 3).toRingHom.eqLocusField (RingHom.id (q.Extension 3))

def baseEmbedding (q : CFSG.PrimePower) : q.Field →ₐ[ZMod q.prime] q.Extension 3 :=
  Classical.choice (FiniteField.nonempty_algHom_of_finrank_dvd (F := ZMod q.prime)
    (K := q.Field) (L := q.Extension 3) (by
      change Module.finrank (ZMod q.prime) (GaloisField q.prime q.exponent) ∣
        Module.finrank (ZMod q.prime) (GaloisField q.prime (3 * q.exponent))
      rw [GaloisField.finrank q.prime (Nat.ne_of_gt q.exponent_pos),
        GaloisField.finrank q.prime (by have := q.exponent_pos; omega)]
      exact dvd_mul_left _ _))

theorem baseEmbedding_fixed (q : CFSG.PrimePower) (x : q.Field) :
    baseEmbedding q x ∈ fixedField q := by
  letI : Fintype q.Field := Fintype.ofFinite _
  have hx : x ^ q.order = x := by
    simpa only [← Nat.card_eq_fintype_card, q.card_field] using FiniteField.pow_card x
  change (baseEmbedding q x) ^ q.order = baseEmbedding q x
  rw [← map_pow, hx]

def baseToFixed (q : CFSG.PrimePower) : q.Field →+* fixedField q where
  toFun x := ⟨baseEmbedding q x, baseEmbedding_fixed q x⟩
  map_one' := Subtype.ext (map_one (baseEmbedding q))
  map_mul' x y := Subtype.ext (map_mul (baseEmbedding q) x y)
  map_zero' := Subtype.ext (map_zero (baseEmbedding q))
  map_add' x y := Subtype.ext (map_add (baseEmbedding q) x y)

theorem fixedField_card_le (q : CFSG.PrimePower) : Nat.card (fixedField q) ≤ q.order := by
  let K := q.Extension 3
  let p : K[X] := Polynomial.X ^ q.order - Polynomial.X
  have hq : 1 < q.order := lt_of_lt_of_le (by decide : 1 < 2)
    (q.prime_isPrime.two_le.trans
      (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime))
  have hp : p ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero K hq
  have he : (fixedField q : Set K) = p.rootSet K := by
    ext x
    rw [Polynomial.mem_rootSet_of_ne hp]
    change (x ^ q.order = x) ↔ Polynomial.aeval x p = 0
    simp only [p, map_sub, map_pow, Polynomial.aeval_X, sub_eq_zero]
  change Nat.card (↥(fixedField q : Set K)) ≤ q.order
  rw [Nat.card_coe_set_eq, he]
  exact (Polynomial.ncard_rootSet_le p K).trans_eq
    (FiniteField.X_pow_card_sub_X_natDegree_eq K hq)

theorem fixedField_card (q : CFSG.PrimePower) : Nat.card (fixedField q) = q.order := by
  apply le_antisymm (fixedField_card_le q)
  rw [← q.card_field]
  exact Nat.card_le_card_of_injective (baseToFixed q) (baseToFixed q).injective

end SymmetricSubgroupAsymptotics.CFSGTrialityFixedField
