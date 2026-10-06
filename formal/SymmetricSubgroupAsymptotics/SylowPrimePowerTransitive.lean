import SymmetricSubgroupAsymptotics.TraceySylowIndices
import SymmetricSubgroupAsymptotics.OrbitQuotientOneTransitive

/-!
# Sylow transitivity in prime-power degree

In a finite transitive action of degree `p^a`, every Sylow `p` subgroup is
transitive.  This is the orbit-valuation consequence needed to apply the
intrinsic binary induced-head theorem to the literal finite frames.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- A Sylow subgroup is transitive in a transitive action whose degree is a
power of its defining prime. -/
theorem sylow_isPretransitive_of_card_eq_prime_pow
    {p a : ℕ} [Fact p.Prime]
    {G X : Type} [Group G] [Finite G] [Finite X] [Nonempty X]
    [MulAction G X] [MulAction.IsPretransitive G X]
    (P : Sylow p G) (hcard : Nat.card X = p ^ a) :
    MulAction.IsPretransitive P X := by
  let O := MulAction.orbitRel.Quotient P X
  letI : Fintype O := Fintype.ofFinite O
  have hcount := traceySylow_orbit_count p P (X := X)
  have hvaluation : (Nat.card X).factorization p = a := by
    rw [hcard, Nat.factorization_pow_self (Fact.out : p.Prime)]
  rw [hvaluation, hcard] at hcount
  have hpowpos : 0 < p ^ a := pow_pos (Fact.out : p.Prime).pos a
  have hle : Nat.card O ≤ 1 := by
    rw [Nat.card_eq_fintype_card]
    apply Nat.le_of_mul_le_mul_right
    · simpa only [O, one_mul] using hcount
    · exact hpowpos
  let x : X := Classical.choice inferInstance
  letI : Nonempty O := ⟨Quotient.mk'' x⟩
  have hpos : 0 < Nat.card O := Nat.card_pos
  have hone : Nat.card O = 1 := by omega
  exact isPretransitive_of_orbitQuotient_card_eq_one hone

/-- Inside an ambient group, a transitive subgroup of prime-power degree
contains an actual prime subgroup which is still transitive.  The returned
subgroup is the image of a Sylow subgroup under the literal inclusion; no
splitting or regular subgroup is chosen. -/
theorem exists_transitive_isPGroup_subgroup_of_card_eq_prime_pow
    {p a : ℕ} [Fact p.Prime]
    {G X : Type} [Group G] [Finite G] [Finite X] [Nonempty X]
    [MulAction G X]
    (K : Subgroup G) [MulAction.IsPretransitive K X]
    (hcard : Nat.card X = p ^ a) :
    ∃ P : Subgroup G,
      IsPGroup p P ∧ P ≤ K ∧ MulAction.IsPretransitive P X := by
  let P₀ : Sylow p K := Classical.choice inferInstance
  let P : Subgroup G := (P₀ : Subgroup K).map K.subtype
  have htrans₀ : MulAction.IsPretransitive P₀ X :=
    sylow_isPretransitive_of_card_eq_prime_pow P₀ hcard
  have htrans : MulAction.IsPretransitive P X := by
    constructor
    intro x y
    obtain ⟨g, hg⟩ := htrans₀.exists_smul_eq x y
    let gP : P := ⟨(g.1 : G), ⟨g.1, g.2, rfl⟩⟩
    exact ⟨gP, hg⟩
  refine ⟨P, P₀.isPGroup'.map K.subtype, ?_, htrans⟩
  rintro g ⟨k, _hk, hkg⟩
  rw [← hkg]
  exact k.2

/-- The binary specialization at the two finite-frame degrees. -/
theorem exists_transitive_binarySubgroup_of_card_eight_or_sixteen
    {G X : Type} [Group G] [Finite G] [Finite X] [Nonempty X]
    [MulAction G X]
    (K : Subgroup G) [MulAction.IsPretransitive K X]
    (hcard : Nat.card X = 8 ∨ Nat.card X = 16) :
    ∃ P : Subgroup G,
      IsPGroup 2 P ∧ P ≤ K ∧ MulAction.IsPretransitive P X := by
  letI : Fact (2 : ℕ).Prime := ⟨Nat.prime_two⟩
  rcases hcard with h8 | h16
  · apply exists_transitive_isPGroup_subgroup_of_card_eq_prime_pow
      (p := 2) (a := 3) K
    simpa only [h8] using (show 8 = 2 ^ (3 : ℕ) by norm_num)
  · apply exists_transitive_isPGroup_subgroup_of_card_eq_prime_pow
      (p := 2) (a := 4) K
    simpa only [h16] using (show 16 = 2 ^ (4 : ℕ) by norm_num)

end SymmetricSubgroupAsymptotics

end
