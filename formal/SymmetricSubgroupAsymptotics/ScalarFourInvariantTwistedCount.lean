import SymmetricSubgroupAsymptotics.ScalarFourHeadCount

/-! Joint counting of invariant and nontrivial C3 characters.  The trace
projection recovers the invariant component from one retained binary
character; its complementary component recovers the twisted F4 map.
Consequently one invariant coordinate and one twisted coordinate jointly
cost only d2(F), rather than the sum of two independent maxima. -/

set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics

private abbrev BinaryScalar := Multiplicative (ZMod 2)

private theorem binary_cancel :
    ∀ a b c : BinaryScalar, a*b=a*c → b=c := by decide +kernel

private theorem scalarFour_binary_trace :
    ∀ (a : BinaryScalar) (v : ScalarFour),
      (a * scalarFourFst v) *
        (a * scalarFourFst (scalarFourTwist 1 v)) *
        (a * scalarFourFst (scalarFourTwist 1 (scalarFourTwist 1 v))) = a := by
  decide

/-- The actual invariant and twisted components for a retained source map.
No replacement of F by an abstract vector space is made. -/
structure ScalarFourInvariantTwistedPair (F : Type*) [Group F] (alpha : F → F) where
  invariant : F →* BinaryScalar
  twisted : F →* ScalarFour
  invariant_fixed : ∀ x, invariant (alpha x) = invariant x
  twisted_action : ∀ x, twisted (alpha x) = scalarFourTwist 1 (twisted x)

namespace ScalarFourInvariantTwistedPair
variable {F : Type*} [Group F] {alpha : F → F}

/-- Sum of the invariant and trace-zero binary characters. -/
def encode (D : ScalarFourInvariantTwistedPair F alpha) : F →* BinaryScalar :=
  D.invariant * scalarFourFst.comp D.twisted

/-- Averaging over the three conjugates is an exact projection onto the
invariant part in characteristic two. -/
theorem trace_encode (D : ScalarFourInvariantTwistedPair F alpha) (x : F) :
    D.encode x * D.encode (alpha x) * D.encode (alpha (alpha x)) =
      D.invariant x := by
  simpa only [encode, MonoidHom.mul_apply, MonoidHom.comp_apply,
    D.invariant_fixed, D.twisted_action] using
    scalarFour_binary_trace (D.invariant x) (D.twisted x)

theorem encode_injective : Function.Injective
    (encode (F := F) (alpha := alpha)) := by
  intro D E h
  have hi : D.invariant = E.invariant := by
    ext x
    rw [← D.trace_encode x, ← E.trace_encode x, h]
  have ht : D.twisted = E.twisted := by
    apply twistedHom_eq_of_fst alpha D.twisted_action E.twisted_action
    ext x
    have hx := DFunLike.congr_fun h x
    change D.invariant x * scalarFourFst (D.twisted x) =
      E.invariant x * scalarFourFst (E.twisted x) at hx
    rw [hi] at hx
    exact binary_cancel (E.invariant x)
      (scalarFourFst (D.twisted x)) (scalarFourFst (E.twisted x)) hx
  cases D
  cases E
  cases hi
  cases ht
  rfl

/-- Exact joint budget for one coordinate of each type. -/
theorem card_le [Finite F] :
    Nat.card (ScalarFourInvariantTwistedPair F alpha) ≤
      2 ^ binaryCharacterRank F := by
  letI : Finite (F →* BinaryScalar) :=
    Finite.of_injective (fun f : F →* BinaryScalar => (f : F → BinaryScalar))
      DFunLike.coe_injective
  letI : Finite (ScalarFourInvariantTwistedPair F alpha) :=
    Finite.of_injective encode encode_injective
  have h := Nat.card_le_card_of_injective encode
    (encode_injective (F := F) (alpha := alpha))
  rw [binaryAbelianizationGroupHom_card] at h
  simpa only [Module.finrank_self, mul_one] using h

/-- Two coordinates of each type, counted jointly. This covers central
binary rank at most two together with two scalar-F4 coordinates. -/
theorem pair_card_le [Finite F] :
    Nat.card (ScalarFourInvariantTwistedPair F alpha ×
      ScalarFourInvariantTwistedPair F alpha) ≤
        2 ^ (2 * binaryCharacterRank F) := by
  rw [Nat.card_prod]
  calc
    Nat.card (ScalarFourInvariantTwistedPair F alpha) *
        Nat.card (ScalarFourInvariantTwistedPair F alpha) ≤
      (2 ^ binaryCharacterRank F) * (2 ^ binaryCharacterRank F) :=
        Nat.mul_le_mul card_le card_le
    _ = 2 ^ (2 * binaryCharacterRank F) := by
      rw [← pow_add]
      congr 1
      omega

end ScalarFourInvariantTwistedPair
end SymmetricSubgroupAsymptotics
end
