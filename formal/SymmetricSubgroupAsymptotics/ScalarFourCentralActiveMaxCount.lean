import SymmetricSubgroupAsymptotics.ScalarFourInvariantTwistedCount

/-! Central and active coordinates share the same original binary character
budget. The bound is their maximum, not their sum; it uses no target split. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.ScalarFourCentralActiveMaxCount
abbrev Binary := Multiplicative (ZMod 2)
variable (F : Type) [Group F] (alpha : F → F)

abbrev Invariant := {f : F →* Binary // ∀ x, f (alpha x)=f x}
abbrev Twisted := {f : F →* ScalarFour // ∀ x, f (alpha x)=scalarFourTwist 1 (f x)}

def pack : Invariant F alpha × Twisted F alpha →
    ScalarFourInvariantTwistedPair F alpha := fun p =>
  ⟨p.1.val,p.2.val,p.1.property,p.2.property⟩

theorem pack_injective : Function.Injective (pack F alpha) := by
  intro p q h
  apply Prod.ext
  · exact Subtype.ext (congrArg ScalarFourInvariantTwistedPair.invariant h)
  · exact Subtype.ext (congrArg ScalarFourInvariantTwistedPair.twisted h)

include alpha in
theorem invariant_twisted_card_le [Finite F] :
    Nat.card (Invariant F alpha) * Nat.card (Twisted F alpha) ≤
      2 ^ binaryCharacterRank F := by
  letI : Finite (F →* Binary) := Finite.of_injective
    (fun f : F →* Binary => (f : F → Binary)) DFunLike.coe_injective
  letI : Finite (F →* ScalarFour) := Finite.of_injective
    (fun f : F →* ScalarFour => (f : F → ScalarFour)) DFunLike.coe_injective
  letI : Finite (ScalarFourInvariantTwistedPair F alpha) :=
    Finite.of_injective ScalarFourInvariantTwistedPair.encode
      ScalarFourInvariantTwistedPair.encode_injective
  rw [← Nat.card_prod]
  exact (Nat.card_le_card_of_injective (pack F alpha) (pack_injective F alpha)).trans
    ScalarFourInvariantTwistedPair.card_le

/-- A finite torsor of central lifts and its actual active quotient maps can
be counted separately, while retaining their shared source rank. -/
theorem max_card_le [Finite F] (c d : ℕ) :
    Nat.card (Invariant F alpha)^c * Nat.card (Twisted F alpha)^d ≤
      2 ^ (max c d * binaryCharacterRank F) := by
  letI : Finite (F →* Binary) := Finite.of_injective
    (fun f : F →* Binary => (f : F → Binary)) DFunLike.coe_injective
  letI : Finite (F →* ScalarFour) := Finite.of_injective
    (fun f : F →* ScalarFour => (f : F → ScalarFour)) DFunLike.coe_injective
  letI : Nonempty (Invariant F alpha) := ⟨⟨1,by intro x; rfl⟩⟩
  letI : Nonempty (Twisted F alpha) := ⟨⟨1,by intro x; exact (map_one _).symm⟩⟩
  have hi : 1≤Nat.card (Invariant F alpha) := Nat.card_pos
  have ht : 1≤Nat.card (Twisted F alpha) := Nat.card_pos
  calc
    _ ≤ Nat.card (Invariant F alpha)^(max c d) *
        Nat.card (Twisted F alpha)^(max c d) :=
      Nat.mul_le_mul (pow_le_pow_right₀ hi (le_max_left c d))
        (pow_le_pow_right₀ ht (le_max_right c d))
    _ = (Nat.card (Invariant F alpha) * Nat.card (Twisted F alpha))^(max c d) :=
      (mul_pow _ _ _).symm
    _ ≤ (2^binaryCharacterRank F)^(max c d) :=
      Nat.pow_le_pow_left (invariant_twisted_card_le F alpha) _
    _ = _ := by rw [← pow_mul, Nat.mul_comm]
end SymmetricSubgroupAsymptotics.ScalarFourCentralActiveMaxCount
