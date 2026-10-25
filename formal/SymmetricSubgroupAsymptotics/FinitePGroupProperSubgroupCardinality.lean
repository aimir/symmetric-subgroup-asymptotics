import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Index

/-! A proper subgroup of an actual finite p-group loses a factor p.
No elementary-abelian or scalar-module structure is required. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.FinitePGroupProperSubgroupCardinality

theorem prime_mul_card_le {G : Type*} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] (hG : IsPGroup p G)
    (C : Subgroup G) (hC : C ≠ ⊤) : p*Nat.card C ≤ Nat.card G := by
  obtain ⟨e,he⟩ := hG.index C
  have hepos : 0 < e := by
    by_contra hn
    have hz : e = 0 := Nat.eq_zero_of_not_pos hn
    apply hC
    apply Subgroup.index_eq_one.mp
    simpa only [hz,pow_zero] using he
  have hp : p ≤ C.index := by
    calc
      p = p^1 := (pow_one p).symm
      _ ≤ p^e := Nat.pow_le_pow_right (Fact.out : p.Prime).pos hepos
      _ = C.index := he.symm
  calc
    p*Nat.card C ≤ C.index*Nat.card C := Nat.mul_le_mul_right _ hp
    _ = Nat.card G := C.index_mul_card

end SymmetricSubgroupAsymptotics.FinitePGroupProperSubgroupCardinality
