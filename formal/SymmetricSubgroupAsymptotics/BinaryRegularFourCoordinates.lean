import SymmetricSubgroupAsymptotics.BinaryPairRankTwoTopOrders
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finiteness

/-! Additive coordinates for an actual regular four-point image.

The group is the literal image supplied by the original action. Its
cardinality and exponent construct a reversible binary coordinate map;
no permutation action is replaced before a point chart transports it.
-/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

abbrev BinaryRegularFourSpace := ZMod 2 × ZMod 2

/-- Coordinates of an actual group of order four and exponent two. -/
def binaryFourCoordinates {V : Type} [Group V] [Finite V]
    (hcard : Nat.card V=4) (hsquare : ∀ v : V,v^2=1) :
    V ≃* Multiplicative BinaryRegularFourSpace := by
  letI : CommGroup V := {
    (inferInstance : Group V) with
    mul_comm := TransitiveTwoRegularOrbitChart.commutative_of_pow_two hsquare }
  letI : Module (ZMod 2) (Additive V) := AddCommGroup.zmodModule (n := 2) (by
    intro v
    change Additive.ofMul (v.toMul^2)=Additive.ofMul 1
    rw [hsquare])
  have hd : Module.finrank (ZMod 2) (Additive V)=2 := by
    apply Nat.pow_right_injective (by decide : 1<(2:ℕ))
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V)
    rw [Nat.card_congr (Additive.toMul : Additive V ≃ V),hcard,Nat.card_zmod] at hc
    exact hc.symm
  let e : Additive V ≃ₗ[ZMod 2] BinaryRegularFourSpace :=
    LinearEquiv.ofFinrankEq _ _ (by
      change Module.finrank (ZMod 2) (Additive V)=
        Module.finrank (ZMod 2) (ZMod 2 × ZMod 2)
      rw [hd,Module.finrank_prod]
      simp)
  refine {
    toEquiv := Additive.ofMul.trans (e.toEquiv.trans Multiplicative.ofAdd)
    map_mul' := ?_ }
  intro a b
  change Multiplicative.ofAdd (e (Additive.ofMul (a*b)))=
    Multiplicative.ofAdd (e (Additive.ofMul a)+e (Additive.ofMul b))
  apply congrArg Multiplicative.ofAdd
  exact e.map_add (Additive.ofMul a) (Additive.ofMul b)

end SymmetricSubgroupAsymptotics
