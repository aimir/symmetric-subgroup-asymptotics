import SymmetricSubgroupAsymptotics.CFSGUnitaryNaturalNormOrbitCardinality
import Mathlib.Algebra.CharP.Two

/-! A literal norm-one trace slice removes at least 96 of the 256
four-dimensional vectors over the binary quadratic extension. No exact
unitary group order or whole norm-shell count is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUnitaryParameters
open CFSGTwistedAUnitaryNaturalRadical CFSGSerreOrdinaryTwists
open CFSGUnitarySignedTraceSliceCardinality

def unitaryIsotropicVectors (q : CFSG.PrimePower) (r : ℕ) :
    Set (Fin (r+1) → q.Extension 2) := {v | unitaryNaturalPair q r v v=0}

theorem unitaryIsotropicVectors_binary_four_card_le (q : CFSG.PrimePower)
    (hq : q.order=2) : Nat.card (unitaryIsotropicVectors q 3) ≤ 160 := by
  have hp : q.prime=2 := by
    have hd : q.prime ∣ 2 := by
      rw [← hq]
      exact dvd_pow_self _ q.exponent_pos.ne'
    exact Nat.le_antisymm (Nat.le_of_dvd (by decide) hd) q.prime_isPrime.two_le
  letI : CharP (q.Extension 2) 2 := by
    simpa only [hp] using (inferInstance : CharP (q.Extension 2) q.prime)
  let Q := hermitianNorm (definingFieldAutomorphism q 2) (middleForm q 1)
  have hQ (w : Fin 2 → q.Extension 2) :
      definingFieldAutomorphism q 2 (Q w) = parity q 1 * Q w :=
    hermitianNorm_sigma (definingFieldAutomorphism q 2)
      (fun a => extension_two_pow_twice q a) (parity q 1) (middleForm q 1)
      (middleForm_hermitian q 1) w
  have hc : definingFieldAutomorphism q 2 (1:q.Extension 2) = parity q 1 * 1 := by
    simp only [map_one, parity, pow_one, CharTwo.neg_eq, one_mul]
  let T := traceSlice q 1 Q 1
  let S := {v : Fin 4 → q.Extension 2 | unitaryNaturalPair q 3 v v=1}
  let f : T → S := fun p => ⟨unitaryNormLevelVector q 1 p.val, by
    exact (unitaryNormLevelVector_norm q 1 p.val).trans p.property.2⟩
  have hf : Function.Injective f := by
    intro x y he
    exact Subtype.ext (unitaryNormLevelVector_injective q 1
      (congrArg (fun v:S => v.val) he))
  have ht := card_traceSlice_lower q 1 (Fin 2 → q.Extension 2) Q hQ 1 hc
  have hcard : Nat.card (Fin 2 → q.Extension 2)=16 := by
    rw [Nat.card_fun, Nat.card_fin, extension_two_card, hq] <;> norm_num
  have h96 : 96 ≤ Nat.card S := by
    have hh := ht.trans (Nat.card_le_card_of_injective f hf)
    simpa only [hcard,hq,Nat.reducePow,Nat.reduceSub,Nat.reduceMul] using hh
  let g : unitaryIsotropicVectors q 3 ⊕ S → (Fin 4 → q.Extension 2) :=
    Sum.elim Subtype.val Subtype.val
  have hg : Function.Injective g := by
    rintro (x|x) (y|y) he
    · exact congrArg Sum.inl (Subtype.ext he)
    · exfalso
      have hh := congrArg (fun v => unitaryNaturalPair q 3 v v) he
      exact zero_ne_one (x.property.symm.trans (hh.trans y.property))
    · exfalso
      have hh := congrArg (fun v => unitaryNaturalPair q 3 v v) he
      exact one_ne_zero (x.property.symm.trans (hh.trans y.property))
    · exact congrArg Sum.inr (Subtype.ext he)
  have hsum := Nat.card_le_card_of_injective g hg
  have htotal : Nat.card (Fin 4 → q.Extension 2)=256 := by
    rw [Nat.card_fun, Nat.card_fin, extension_two_card, hq] <;> norm_num
  rw [Nat.card_sum,htotal] at hsum
  omega

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
