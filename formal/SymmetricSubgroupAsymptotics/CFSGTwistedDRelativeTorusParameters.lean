import SymmetricSubgroupAsymptotics.CFSGTwistedDNormOneUnits
import SymmetricSubgroupAsymptotics.CFSGTwistedA2NormSurjectivity
import Mathlib.Algebra.Group.Prod

/-! The actual diagonal parameter map c ↦ (Norm(c),sigma(c)/c).
Both components are literal homomorphisms on the quadratic extension's
unit group. Its kernel has scalar square one. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeTorusParameters
open CFSGSerreOrdinaryTwists CFSGTwistedA2FixedField CFSGTwistedANaturalMatrices
open CFSGTwistedDNormOneUnits

def unitFrobenius (q : CFSG.PrimePower) : (q.Extension 2)ˣ →* (q.Extension 2)ˣ :=
  Units.map (definingFieldAutomorphism q 2).toMonoidHom

theorem unitFrobenius_val (q : CFSG.PrimePower) (c : (q.Extension 2)ˣ) :
    (unitFrobenius q c : q.Extension 2) = definingFieldAutomorphism q 2 (c : q.Extension 2) := rfl

theorem unitFrobenius_pow (q : CFSG.PrimePower) (c : (q.Extension 2)ˣ) :
    unitFrobenius q c = c ^ q.order := by
  apply Units.ext
  change definingFieldAutomorphism q 2 (c : q.Extension 2) = (c : q.Extension 2) ^ q.order
  exact definingFieldAutomorphism_apply q 2 c

theorem unitFrobenius_twice (q : CFSG.PrimePower) (c : (q.Extension 2)ˣ) :
    unitFrobenius q (unitFrobenius q c) = c := by
  apply Units.ext
  change definingFieldAutomorphism q 2
    (definingFieldAutomorphism q 2 (c : q.Extension 2)) = (c : q.Extension 2)
  simpa only [definingFieldAutomorphism_apply] using extension_two_pow_twice q (c : q.Extension 2)

def normHom (q : CFSG.PrimePower) : (q.Extension 2)ˣ →* (fixedField q)ˣ :=
  Units.map (Algebra.norm (fixedField q))

theorem normHom_val (q : CFSG.PrimePower) (c : (q.Extension 2)ˣ) :
    (((normHom q c : (fixedField q)ˣ) : fixedField q) : q.Extension 2) =
      (c : q.Extension 2) * definingFieldAutomorphism q 2 (c : q.Extension 2) := by
  have h := FiniteField.algebraMap_norm_eq_pow
    (K := fixedField q) (K' := q.Extension 2) (x := (c : q.Extension 2))
  rw [extension_two_card, fixedField_card, CFSGTwistedA2UnipotentArrays.normExponent] at h
  change (((Algebra.norm (fixedField q) (c : q.Extension 2)) : fixedField q) : q.Extension 2) = _
  simpa only [pow_succ, definingFieldAutomorphism_apply, mul_comm] using h

def quotientUnitHom (q : CFSG.PrimePower) : (q.Extension 2)ˣ →* (q.Extension 2)ˣ where
  toFun c := unitFrobenius q c * c⁻¹
  map_one' := by rw [map_one, inv_one, mul_one]
  map_mul' c d := by
    rw [map_mul, mul_inv_rev]
    ac_rfl

theorem quotientUnitHom_mem (q : CFSG.PrimePower) (c : (q.Extension 2)ˣ) :
    quotientUnitHom q c ∈ normOneUnits q := by
  change (unitFrobenius q c * c⁻¹) ^ (q.order + 1) = 1
  rw [pow_succ, ← unitFrobenius_pow, map_mul, map_inv, unitFrobenius_twice]
  group

def quotientHom (q : CFSG.PrimePower) : (q.Extension 2)ˣ →* normOneUnits q :=
  (quotientUnitHom q).codRestrict (normOneUnits q) (quotientUnitHom_mem q)

def torusParameterHom (q : CFSG.PrimePower) :
    (q.Extension 2)ˣ →* (fixedField q)ˣ × normOneUnits q :=
  (normHom q).prod (quotientHom q)

theorem kernel_square_one (q : CFSG.PrimePower) (c : (q.Extension 2)ˣ)
    (hc : c ∈ (torusParameterHom q).ker) : (c : q.Extension 2) ^ 2 = 1 := by
  have h : torusParameterHom q c = 1 := hc
  have hn : normHom q c = 1 := congrArg Prod.fst h
  have hz := congrArg (fun x : (fixedField q)ˣ × normOneUnits q => x.2.val) h
  change unitFrobenius q c * c⁻¹ = 1 at hz
  have hs : unitFrobenius q c = c := by
    have he := congrArg (fun u : (q.Extension 2)ˣ => u * c) hz
    simpa only [mul_assoc, inv_mul_cancel, mul_one, one_mul] using he
  have hsf : definingFieldAutomorphism q 2 (c : q.Extension 2) = (c : q.Extension 2) :=
    congrArg (fun u : (q.Extension 2)ˣ => (u : q.Extension 2)) hs
  have hnf := congrArg (fun u : (fixedField q)ˣ => ((u : fixedField q) : q.Extension 2)) hn
  change (((normHom q c : (fixedField q)ˣ) : fixedField q) : q.Extension 2) = 1 at hnf
  rw [normHom_val, hsf] at hnf
  simpa only [pow_two] using hnf

end SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeTorusParameters
