import SymmetricSubgroupAsymptotics.ScalarFourInvariantC4TwistedCount

/-! Invariant central C4 and cubic-active F4 coordinates are charged by
their maximum against the SAME exact C4-character count of the source. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.ScalarFourCentralC4ActiveMaxCount
variable (F : Type) [Group F] (alpha : F → F)

abbrev Invariant := {f : F →* InvariantC4Scalar // ∀ x,f (alpha x)=f x}
abbrev Twisted := {f : F →* ScalarFour // ∀ x,f (alpha x)=scalarFourTwist 1 (f x)}

def pack : Invariant F alpha × Twisted F alpha →
    ScalarFourInvariantC4TwistedPair F alpha := fun p =>
  ⟨p.1.val,p.2.val,p.1.property,p.2.property⟩

theorem pack_injective : Function.Injective (pack F alpha) := by
  intro p q h
  apply Prod.ext
  · exact Subtype.ext (congrArg ScalarFourInvariantC4TwistedPair.invariant h)
  · exact Subtype.ext (congrArg ScalarFourInvariantC4TwistedPair.twisted h)

theorem invariant_twisted_card_le [Finite F] :
    Nat.card (Invariant F alpha) * Nat.card (Twisted F alpha) ≤
      Nat.card (F →* InvariantC4Scalar) := by
  letI : Finite (F →* InvariantC4Scalar) := Finite.of_injective
    (fun f : F →* InvariantC4Scalar => (f : F → InvariantC4Scalar)) DFunLike.coe_injective
  letI : Finite (F →* ScalarFour) := Finite.of_injective
    (fun f : F →* ScalarFour => (f : F → ScalarFour)) DFunLike.coe_injective
  letI : Finite (ScalarFourInvariantC4TwistedPair F alpha) :=
    Finite.of_injective ScalarFourInvariantC4TwistedPair.encode
      ScalarFourInvariantC4TwistedPair.encode_injective
  rw [←Nat.card_prod]
  exact (Nat.card_le_card_of_injective (pack F alpha) (pack_injective F alpha)).trans
    ScalarFourInvariantC4TwistedPair.card_le

/-- MAX(c,d), without an independent central-coordinate rank charge. -/
theorem max_card_le [Finite F] (c d : ℕ) :
    Nat.card (Invariant F alpha)^c * Nat.card (Twisted F alpha)^d ≤
      Nat.card (F →* InvariantC4Scalar)^(max c d) := by
  letI : Finite (F →* InvariantC4Scalar) := Finite.of_injective
    (fun f : F →* InvariantC4Scalar => (f : F → InvariantC4Scalar)) DFunLike.coe_injective
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
    _ ≤ _ := Nat.pow_le_pow_left (invariant_twisted_card_le F alpha) _

end SymmetricSubgroupAsymptotics.ScalarFourCentralC4ActiveMaxCount
