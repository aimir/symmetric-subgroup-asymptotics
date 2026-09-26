import SymmetricSubgroupAsymptotics.PrimeCharacterGenerators
import SymmetricSubgroupAsymptotics.PrimeCharacterSubgroupCapacity
import Mathlib.GroupTheory.PGroup

/-! Actual order consequences of an evaluation-kernel identity. The
elementary quotient is the image of the original evaluation map, and
the subgroup order is that of the actual derived subgroup. No ambient
group table, p-group premise or numerical profile is supplied. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable (p : ℕ) [Fact p.Prime] {G : Type*} [Group G] [Finite G]

/-- The literal abelianization has the exact order of the actual prime
character dual when the evaluation kernel is precisely the derived group. -/
theorem card_quotient_commutator_of_evaluationKernel_eq
    (hkernel : (primeAbelianizationGroupMap p G).ker = commutator G) :
    Nat.card (G ⧸ commutator G) =
      p ^ Module.finrank (ZMod p) (PrimeCharacters p G) := by
  rw [← hkernel, Nat.card_congr
    (QuotientGroup.quotientKerEquivOfSurjective (primeAbelianizationGroupMap p G)
      (primeAbelianizationGroupMap_surjective p G)).toEquiv]
  change Nat.card (PrimeAbelianization p G) = _
  rw [Module.natCard_eq_pow_finrank (K := ZMod p)
    (V := PrimeAbelianization p G), Subspace.dual_finrank_eq, Nat.card_zmod]

/-- Exact prime-power order of the original group, rather than only an
upper bound on its order. -/
theorem card_eq_prime_pow_of_evaluationKernel_eq
    (hkernel : (primeAbelianizationGroupMap p G).ker = commutator G)
    (a : ℕ) (hderived : Nat.card (commutator G) = p ^ a) :
    Nat.card G = p ^ (Module.finrank (ZMod p) (PrimeCharacters p G) + a) := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (commutator G),
    card_quotient_commutator_of_evaluationKernel_eq p hkernel, hderived, pow_add]

/-- The p-group property follows from the exact order factorization;
it is not inferred from an order upper bound. -/
theorem isPGroup_of_evaluationKernel_eq
    (hkernel : (primeAbelianizationGroupMap p G).ker = commutator G)
    (a : ℕ) (hderived : Nat.card (commutator G) = p ^ a) :
    IsPGroup p G :=
  IsPGroup.of_card (card_eq_prime_pow_of_evaluationKernel_eq p hkernel a hderived)

/-- The original finite tuple may repeat elements. Its literal closure
still bounds the whole prime character rank by the number of entries. -/
theorem primeCharacterRank_le_generating_tuple {ι : Type*} [Fintype ι]
    (g : ι → G) (hgen : Subgroup.closure (Set.range g) = ⊤) :
    Module.finrank (ZMod p) (PrimeCharacters p G) ≤ Fintype.card ι := by
  classical
  let S : Finset G := Finset.univ.image g
  have hS : (S : Set G) = Set.range g := by
    ext x
    simp [S]
  have hspan : Subgroup.closure (S : Set G) = ⊤ := by
    rw [hS]
    exact hgen
  exact (primeCharacterRank_le_generators p S hspan).trans
    (by simpa only [S, Finset.card_univ] using
      (Finset.card_image_le (s := Finset.univ) (f := g)))

/-- An actual generating tuple bounds the literal derived quotient. -/
theorem card_quotient_commutator_le_of_evaluationKernel_eq
    {ι : Type*} [Fintype ι] (g : ι → G)
    (hgen : Subgroup.closure (Set.range g) = ⊤)
    (hkernel : (primeAbelianizationGroupMap p G).ker = commutator G) :
    Nat.card (G ⧸ commutator G) ≤ p ^ Fintype.card ι := by
  rw [card_quotient_commutator_of_evaluationKernel_eq p hkernel]
  exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos
    (primeCharacterRank_le_generating_tuple p g hgen)

/-- The original tuple and the certified derived order give an ambient
order budget without enumerating the ambient group. -/
theorem card_le_prime_pow_of_evaluationKernel_eq
    {ι : Type*} [Fintype ι] (g : ι → G)
    (hgen : Subgroup.closure (Set.range g) = ⊤)
    (hkernel : (primeAbelianizationGroupMap p G).ker = commutator G)
    (a : ℕ) (hderived : Nat.card (commutator G) = p ^ a) :
    Nat.card G ≤ p ^ (Fintype.card ι + a) := by
  rw [card_eq_prime_pow_of_evaluationKernel_eq p hkernel a hderived]
  exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos
    (Nat.add_le_add_right (primeCharacterRank_le_generating_tuple p g hgen) a)

end SymmetricSubgroupAsymptotics
