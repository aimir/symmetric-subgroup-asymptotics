import SymmetricSubgroupAsymptotics.CFSGCubicNormTorusScalars
import SymmetricSubgroupAsymptotics.CFSGTrialityFixedField
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Ring

/-! The actual cubic Frobenius norm gives every pair of torus scalar
coordinates over the literal triality fixed field. Oddness of q²+q+1
supplies a norm-one square correction, including q=2. No group-order
formula or surjectivity of a fixed-point functor is used. The action of
literal torus words must still be matched with this scalar map. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityNormTorusScalars
open CFSGTrialityFixedField CFSGSerreOrdinaryTwists

def normFieldHom (q : CFSG.PrimePower) : q.Extension 3 →* fixedField q where
  toFun x := ⟨x * definingFieldAutomorphism q 3 x *
    definingFieldAutomorphism q 3 (definingFieldAutomorphism q 3 x), by
      change definingFieldAutomorphism q 3
        (x * definingFieldAutomorphism q 3 x *
          definingFieldAutomorphism q 3 (definingFieldAutomorphism q 3 x)) = _
      simp only [map_mul, sigma_thrice]
      ac_rfl⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' x y := by
    apply Subtype.ext
    change (x * y) * definingFieldAutomorphism q 3 (x * y) *
      definingFieldAutomorphism q 3 (definingFieldAutomorphism q 3 (x * y)) =
      (x * definingFieldAutomorphism q 3 x *
        definingFieldAutomorphism q 3 (definingFieldAutomorphism q 3 x)) *
      (y * definingFieldAutomorphism q 3 y *
        definingFieldAutomorphism q 3 (definingFieldAutomorphism q 3 y))
    simp only [map_mul]
    ac_rfl

def normUnits (q : CFSG.PrimePower) : (q.Extension 3)ˣ →* (fixedField q)ˣ :=
  Units.map (normFieldHom q)

def embedUnits (q : CFSG.PrimePower) : (fixedField q)ˣ →* (q.Extension 3)ˣ :=
  Units.map (fixedField q).subtype.toMonoidHom

theorem normUnits_embed (q : CFSG.PrimePower) (a : (fixedField q)ˣ) :
    normUnits q (embedUnits q a) = a ^ 3 := by
  apply Units.ext
  apply Subtype.ext
  change a.val.val * definingFieldAutomorphism q 3 a.val.val *
    definingFieldAutomorphism q 3 (definingFieldAutomorphism q 3 a.val.val) = a.val.val ^ 3
  have ha : definingFieldAutomorphism q 3 a.val.val = a.val.val := a.val.property
  rw [ha, ha]
  simp [pow_succ, mul_assoc]

theorem embed_normUnits_power (q : CFSG.PrimePower) (u : (q.Extension 3)ˣ) :
    embedUnits q (normUnits q u) = u ^ (q.order ^ 2 + q.order + 1) := by
  apply Units.ext
  change (u : q.Extension 3) * definingFieldAutomorphism q 3 (u : q.Extension 3) *
    definingFieldAutomorphism q 3 (definingFieldAutomorphism q 3 (u : q.Extension 3)) = _
  change (u : q.Extension 3) * (u : q.Extension 3) ^ q.order *
    ((u : q.Extension 3) ^ q.order) ^ q.order = _
  rw [← pow_mul]
  calc
    _ = (u : q.Extension 3) ^ (1 + q.order + q.order * q.order) := by
      rw [pow_add, pow_add, pow_one]
    _ = (u : q.Extension 3) ^ (q.order ^ 2 + q.order + 1) := by
      congr 1
      ring

theorem norm_exponent_odd (q : CFSG.PrimePower) : Odd (q.order ^ 2 + q.order + 1) := by
  have h := (Nat.even_mul_succ_self q.order).add_one
  convert h using 1 <;> ring

theorem scalarMap_surjective (q : CFSG.PrimePower) :
    Function.Surjective
      (CFSGCubicNormTorusScalars.scalarMap (embedUnits q) (normUnits q)) :=
  CFSGCubicNormTorusScalars.scalarMap_surjective_of_odd_norm_power
    (embedUnits q) (normUnits q) (normUnits_embed q)
    (q.order ^ 2 + q.order + 1) (norm_exponent_odd q) (embed_normUnits_power q)

end SymmetricSubgroupAsymptotics.CFSGTrialityNormTorusScalars
