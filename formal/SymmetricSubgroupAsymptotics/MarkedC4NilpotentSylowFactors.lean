import SymmetricSubgroupAsymptotics.MarkedC4CoprimePhysicalGrid
import Mathlib.GroupTheory.Nilpotent
import Mathlib.Data.Nat.GCD.BigOperators

/-! Binary/odd factors are constructed from the actual Sylow decomposition
of a finite nilpotent group. No product chart is assumed as an input. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.MarkedC4.NilpotentSylowFactors

variable (G : Type) [Group G] [Finite G] [Group.IsNilpotent G]
abbrev Primes := (Nat.card G).primeFactors
abbrev Fiber (p : Primes G) := ∀ S : Sylow (p : ℕ) G, S
abbrev Binary := ∀ p : {p : Primes G // (p : ℕ)=2}, Fiber G p.1
abbrev OddFactor := ∀ p : {p : Primes G // (p : ℕ)≠2}, Fiber G p.1

def splitPrimeProduct : (∀ p : Primes G, Fiber G p) ≃* Binary G × OddFactor G where
  toEquiv := Equiv.piEquivPiSubtypeProd (fun p : Primes G => (p : ℕ)=2) (Fiber G)
  map_mul' _ _ := rfl

/-- Ordinary nilpotence supplies all normal Sylows, and hence the actual
binary/odd product equivalence. -/
def equiv : G ≃* Binary G × OddFactor G :=
  (Sylow.directProductOfNormal (G := G) (fun {p} [Fact p.Prime] S =>
    Sylow.normal_of_normalizerCondition (Group.normalizerCondition_of_isNilpotent (G := G)) S)).symm.trans
      (splitPrimeProduct G)

private theorem pi_isPGroup {p : ℕ} [Fact p.Prime] {I : Type} [Fintype I]
    (V : I → Type) [∀ i, Group (V i)] [∀ i, Finite (V i)]
    (h : ∀ i, IsPGroup p (V i)) : IsPGroup p (∀ i,V i) := by
  choose n hn using fun i => (IsPGroup.iff_card.mp (h i))
  apply IsPGroup.of_card (n := ∑ i,n i)
  rw [Nat.card_pi]
  simp_rw [hn]
  exact Finset.prod_pow_eq_pow_sum Finset.univ n p

theorem binary_isPGroup : IsPGroup 2 (Binary G) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Fintype {p : Primes G // (p : ℕ)=2} := Fintype.ofFinite _
  apply pi_isPGroup (fun p : {p : Primes G // (p : ℕ)=2} => Fiber G p.1)
  intro p
  letI : Fintype (Sylow (p.1 : ℕ) G) := Fintype.ofFinite _
  apply pi_isPGroup (fun S : Sylow (p.1 : ℕ) G => S)
  intro S
  simpa only [p.2] using S.isPGroup'

/-- Every odd-factor cardinal is coprime to four, including the empty
prime product of a binary nilpotent group. -/
theorem odd_card_coprime_four : Nat.Coprime (Nat.card (OddFactor G)) 4 := by
  letI : Fintype {p : Primes G // (p : ℕ)≠2} := Fintype.ofFinite _
  rw [Nat.card_pi]
  apply Nat.Coprime.prod_left
  intro p _
  letI : Fact (Nat.Prime (p.1 : ℕ)) := ⟨Nat.prime_of_mem_primeFactors p.1.2⟩
  letI : Fintype (Sylow (p.1 : ℕ) G) := Fintype.ofFinite _
  rw [Nat.card_pi]
  apply Nat.Coprime.prod_left
  intro S _
  obtain ⟨n,hn⟩ := IsPGroup.iff_card.mp S.isPGroup'
  change Nat.Coprime (Nat.card (S : Subgroup G)) 4
  rw [hn]
  have hp : Nat.Coprime (p.1 : ℕ) 2 :=
    (Nat.coprime_primes (Nat.prime_of_mem_primeFactors p.1.2) Nat.prime_two).mpr p.2
  simpa using hp.pow n 2

theorem factors_coprime : Nat.Coprime (Nat.card (Binary G)) (Nat.card (OddFactor G)) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n,hn⟩ := IsPGroup.iff_card.mp (binary_isPGroup G)
  rw [hn]
  have ho : Nat.Coprime (Nat.card (OddFactor G)) 2 :=
    Nat.Coprime.of_dvd_right (by decide : 2∣4) (odd_card_coprime_four G)
  exact ho.symm.pow_left n

/-- The same actual factors meet the exact coprime physical-grid premises. -/
def orbitGrid {X : Type} [MulAction (Binary G × OddFactor G) X] (x : X) :=
  CoprimePhysicalGrid.orbitGrid (factors_coprime G) x

end SymmetricSubgroupAsymptotics.MarkedC4.NilpotentSylowFactors
