import SymmetricSubgroupAsymptotics.CFSGUnitaryRankTwoCentralUpper
import SymmetricSubgroupAsymptotics.CFSGTwistedA2UnipotentParameters
import SymmetricSubgroupAsymptotics.CFSGTwistedA2TorusAction
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! The kernel of the literal rank-two torus in the original central
quotient has at most three elements.  This is derived from its action
on an actual unipotent with first parameter one, not a centre formula. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent CFSGSerreOrdinaryTwists
open CFSGTwistedA2DiagonalTorus

theorem rankTwoProjectiveTorus_kernel_cube (q : CFSG.PrimePower) (hq : 3 ≤ q.order)
    (z : (q.Extension 2)ˣ) (hz : z ∈ (rankTwoProjectiveTorus q hq).ker) :
    z ^ 3 = 1 := by
  let b := CFSGTwistedA2UnipotentParameters.particular q hq 1
  have hb := CFSGTwistedA2UnipotentParameters.particular_spec q hq 1
  let u : naturalUnipotent 2 q :=
    ⟨CFSGTwistedA2UnipotentArrays.upperNatural (q.Extension 2)
      (definingFieldAutomorphism q 2) 1 b,
      rankTwoOldUpper_le q ⟨1, b, hb, rfl⟩⟩
  have hc : rankTwoDerivedCover q hq (rankTwoNaturalTorus q z) ∈
      Subgroup.center (commutator (Fixed 2 q)) := (QuotientGroup.eq_one_iff _).mp hz
  have he := rankTwo_central_cover_conjugates_upper q hq (rankTwoNaturalTorus q z) hc u
  change torusNatural (q.Extension 2) (definingFieldAutomorphism q 2) z *
      CFSGTwistedA2UnipotentArrays.upperNatural (q.Extension 2)
        (definingFieldAutomorphism q 2) 1 b *
      (torusNatural (q.Extension 2) (definingFieldAutomorphism q 2) z)⁻¹ = _ at he
  rw [torus_conjugate_upper _ _ (fun x => extension_two_pow_twice q x) z (Units.ne_zero z)] at he
  have hw := congrArg (fun x : NaturalElementary (q.Extension 2) 2 =>
    (x.val : Mat (q.Extension 2) 2) 0 1) he
  change (CFSGTwistedA2UnipotentArrays.upperNatural (q.Extension 2)
      (definingFieldAutomorphism q 2)
      (firstWeight (q.Extension 2) (definingFieldAutomorphism q 2) (z : q.Extension 2) * 1)
      (centralWeight (q.Extension 2) (definingFieldAutomorphism q 2) (z : q.Extension 2) * b)).val.val 0 1 =
    (CFSGTwistedA2UnipotentArrays.upperNatural (q.Extension 2)
      (definingFieldAutomorphism q 2) 1 b).val.val 0 1 at hw
  rw [CFSGTwistedA2UnipotentArrays.upperNatural_val,
    CFSGTwistedA2UnipotentArrays.upperNatural_val] at hw
  have hw1 : firstWeight (q.Extension 2) (definingFieldAutomorphism q 2) z = 1 := by
    simpa [CFSGTwistedA2UnipotentArrays.upperArray] using hw
  have hs : (z : q.Extension 2) ^ 2 = definingFieldAutomorphism q 2 z :=
    (div_eq_one_iff_eq ((map_ne_zero _).mpr (Units.ne_zero z))).mp hw1
  have hh := congrArg (definingFieldAutomorphism q 2) hs
  rw [map_pow] at hh
  have hi : definingFieldAutomorphism q 2 (definingFieldAutomorphism q 2 (z : q.Extension 2)) =
      (z : q.Extension 2) := extension_two_pow_twice q z
  rw [hi, ← hs, ← pow_mul] at hh
  apply Units.ext
  change (z : q.Extension 2) ^ 3 = 1
  apply mul_right_cancel₀ (Units.ne_zero z)
  simpa only [← pow_succ, one_mul] using hh

theorem rankTwoProjectiveTorus_kernel_card_le (q : CFSG.PrimePower) (hq : 3 ≤ q.order) :
    Nat.card (rankTwoProjectiveTorus q hq).ker ≤ 3 := by
  let f : (rankTwoProjectiveTorus q hq).ker →
      (powMonoidHom 3 : (q.Extension 2)ˣ →* (q.Extension 2)ˣ).ker :=
    fun z => ⟨z.val, rankTwoProjectiveTorus_kernel_cube q hq z.val z.property⟩
  have hf : Function.Injective f := by
    intro z w h
    have hv : z.val = w.val := congrArg
      (fun a : (powMonoidHom 3 : (q.Extension 2)ˣ →* (q.Extension 2)ˣ).ker => a.val) h
    exact Subtype.ext hv
  have hc := Nat.card_le_card_of_injective f hf
  rw [IsCyclic.card_powMonoidHom_ker] at hc
  exact hc.trans (Nat.gcd_le_right _ (by decide))

theorem rankTwoProjectiveTorus_card_lower (q : CFSG.PrimePower) (hq : 3 ≤ q.order) :
    q.order ^ 2 - 1 ≤ 3 * Nat.card (rankTwoProjectiveTorus q hq).range := by
  have he : Nat.card (q.Extension 2)ˣ =
      Nat.card (rankTwoProjectiveTorus q hq).ker *
        Nat.card (rankTwoProjectiveTorus q hq).range := by
    rw [← (rankTwoProjectiveTorus q hq).ker.card_mul_index, Subgroup.index_ker]
  have hc := Nat.mul_le_mul_right (Nat.card (rankTwoProjectiveTorus q hq).range)
    (rankTwoProjectiveTorus_kernel_card_le q hq)
  rw [← he, Nat.card_units, extension_two_card] at hc
  exact hc

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
