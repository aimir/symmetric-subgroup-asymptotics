import SymmetricSubgroupAsymptotics.ElementaryBinaryTransitiveNormalRank
import SymmetricSubgroupAsymptotics.SylowPrimePowerTransitive

/-! An actual elementary Sylow two-subgroup in a faithful transitive
prime-power action is regular on the SAME original points. Thus each
original point stabilizer has exactly the Sylow index, which is odd.
No primitive-group recognition or supplied cardinality certificate occurs. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.ElementarySylowPointStabilizerOrder

variable {G X : Type} [Group G] [Finite G] [Finite X] [Nonempty X]
    [MulAction G X] [FaithfulSMul G X] [MulAction.IsPretransitive G X]

theorem stabilizer_card_eq_sylow_index (P : Sylow 2 G)
    (hel : ∀ g : P, g^2 = 1) (k : ℕ) (hcard : Nat.card X = 2^k) (x : X) :
    Nat.card (MulAction.stabilizer G x) = (P : Subgroup G).index := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : MulAction.IsPretransitive P X := sylow_isPretransitive_of_card_eq_prime_pow P hcard
  have hPcard : Nat.card P = Nat.card X :=
    ElementaryBinaryTransitiveNormalRank.card_eq_degree
      (BinarySquareActionStructure.squaresActTrivially_iff_pow_two.mpr hel) x
  have hPmul := (P : Subgroup G).card_mul_index
  rw [hPcard] at hPmul
  have hHmul := (MulAction.stabilizer G x).card_mul_index
  rw [MulAction.index_stabilizer_of_transitive G x] at hHmul
  have he : Nat.card X * Nat.card (MulAction.stabilizer G x) =
      Nat.card X * (P : Subgroup G).index := by
    calc
      Nat.card X * Nat.card (MulAction.stabilizer G x) =
          Nat.card (MulAction.stabilizer G x) * Nat.card X := Nat.mul_comm _ _
      _ = Nat.card G := hHmul
      _ = Nat.card X * (P : Subgroup G).index := hPmul.symm
  exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := X)) he

theorem two_not_dvd_stabilizer_card (P : Sylow 2 G)
    (hel : ∀ g : P, g^2 = 1) (k : ℕ) (hcard : Nat.card X = 2^k) (x : X) :
    ¬2 ∣ Nat.card (MulAction.stabilizer G x) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [stabilizer_card_eq_sylow_index P hel k hcard x]
  exact P.not_dvd_index

end SymmetricSubgroupAsymptotics.ElementarySylowPointStabilizerOrder
