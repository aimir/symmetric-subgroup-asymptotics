import SymmetricSubgroupAsymptotics.ScalarFourInvariantTwistedCount

/-! One invariant C4 coordinate and one cubic-twisted F4 coordinate share
one ACTUAL C4-character budget. The target homomorphism count is retained;
no replacement by binary character rank is made. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics

abbrev InvariantC4Scalar := Multiplicative (ZMod 4)

/-- The injective additive doubling map F2 -> Z/4, in multiplicative form. -/
def binaryIntoC4 : Multiplicative (ZMod 2) →* InvariantC4Scalar where
  toFun x := Multiplicative.ofAdd (2 * (x.toAdd.val : ZMod 4))
  map_one' := by decide
  map_mul' := by intro x y; revert x y; decide +kernel

theorem binaryIntoC4_injective : Function.Injective binaryIntoC4 := by
  intro x y
  revert x y
  decide +kernel

private theorem c4_cube_injective :
    ∀ a b : InvariantC4Scalar, a^3=b^3 → a=b := by decide +kernel

private theorem scalarFour_c4_trace :
    ∀ (a : InvariantC4Scalar) (v : ScalarFour),
      (a * binaryIntoC4 (scalarFourFst v)) *
        (a * binaryIntoC4 (scalarFourFst (scalarFourTwist 1 v))) *
        (a * binaryIntoC4 (scalarFourFst (scalarFourTwist 1 (scalarFourTwist 1 v)))) =
      a^3 := by decide +kernel

structure ScalarFourInvariantC4TwistedPair (F : Type*) [Group F] (alpha : F → F) where
  invariant : F →* InvariantC4Scalar
  twisted : F →* ScalarFour
  invariant_fixed : ∀ x, invariant (alpha x)=invariant x
  twisted_action : ∀ x, twisted (alpha x)=scalarFourTwist 1 (twisted x)

namespace ScalarFourInvariantC4TwistedPair
variable {F : Type*} [Group F] {alpha : F → F}

def encode (D : ScalarFourInvariantC4TwistedPair F alpha) : F →* InvariantC4Scalar :=
  D.invariant * binaryIntoC4.comp (scalarFourFst.comp D.twisted)

/-- Cubic trace is multiplication by three on the invariant C4 character;
three is invertible modulo four. -/
theorem trace_encode (D : ScalarFourInvariantC4TwistedPair F alpha) (x : F) :
    D.encode x * D.encode (alpha x) * D.encode (alpha (alpha x)) =
      (D.invariant x)^3 := by
  simpa only [encode,MonoidHom.mul_apply,MonoidHom.comp_apply,
    D.invariant_fixed,D.twisted_action] using
      scalarFour_c4_trace (D.invariant x) (D.twisted x)

theorem encode_injective : Function.Injective
    (encode (F := F) (alpha := alpha)) := by
  intro D E h
  have hi : D.invariant=E.invariant := by
    apply MonoidHom.ext
    intro x
    have hc : (D.invariant x)^3=(E.invariant x)^3 := by
      rw [←D.trace_encode x,←E.trace_encode x,h]
    exact c4_cube_injective (D.invariant x) (E.invariant x) hc
  have ht : D.twisted=E.twisted := by
    apply twistedHom_eq_of_fst alpha D.twisted_action E.twisted_action
    ext x
    have hx := DFunLike.congr_fun h x
    change D.invariant x * binaryIntoC4 (scalarFourFst (D.twisted x)) =
      E.invariant x * binaryIntoC4 (scalarFourFst (E.twisted x)) at hx
    rw [hi] at hx
    exact binaryIntoC4_injective (mul_left_cancel hx)
  cases D
  cases E
  cases hi
  cases ht
  rfl

/-- The retained exact C4 homomorphism count, valid for the original F. -/
theorem card_le [Finite F] :
    Nat.card (ScalarFourInvariantC4TwistedPair F alpha) ≤
      Nat.card (F →* InvariantC4Scalar) := by
  letI : Finite (F →* InvariantC4Scalar) := Finite.of_injective
    (fun f : F →* InvariantC4Scalar => (f : F → InvariantC4Scalar)) DFunLike.coe_injective
  exact Nat.card_le_card_of_injective encode
    (encode_injective (F := F) (alpha := alpha))

end ScalarFourInvariantC4TwistedPair
end SymmetricSubgroupAsymptotics
