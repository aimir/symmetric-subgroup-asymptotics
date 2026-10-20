import SymmetricSubgroupAsymptotics.MarkedC4NilpotentSylowFactors

/-! An arbitrary prime factor and its coprime complement in the literal
Sylow product of a finite nilpotent group. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace SymmetricSubgroupAsymptotics.NilpotentPrimeFactorSplit
open MarkedC4.NilpotentSylowFactors

variable (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Finite G] [Group.IsNilpotent G]

abbrev PrimePart := ∀ q : {q : Primes G // (q : ℕ) = p}, Fiber G q.1
abbrev Complement := ∀ q : {q : Primes G // (q : ℕ) ≠ p}, Fiber G q.1

def splitPrimeProduct : (∀ q : Primes G, Fiber G q) ≃* PrimePart p G × Complement p G where
  toEquiv := Equiv.piEquivPiSubtypeProd (fun q : Primes G => (q : ℕ) = p) (Fiber G)
  map_mul' _ _ := rfl

def equiv : G ≃* PrimePart p G × Complement p G :=
  (Sylow.directProductOfNormal (G := G) (fun {q} [Fact q.Prime] S =>
    Sylow.normal_of_normalizerCondition (Group.normalizerCondition_of_isNilpotent (G := G)) S)).symm.trans
      (splitPrimeProduct p G)

private theorem pi_isPGroup {q : ℕ} [Fact q.Prime] {I : Type} [Fintype I]
    (V : I → Type) [∀ i, Group (V i)] [∀ i, Finite (V i)]
    (h : ∀ i, IsPGroup q (V i)) : IsPGroup q (∀ i, V i) := by
  choose n hn using fun i => IsPGroup.iff_card.mp (h i)
  apply IsPGroup.of_card (n := ∑ i, n i)
  rw [Nat.card_pi]
  simp_rw [hn]
  exact Finset.prod_pow_eq_pow_sum Finset.univ n q

theorem primePart_isPGroup : IsPGroup p (PrimePart p G) := by
  letI : Fintype {q : Primes G // (q : ℕ) = p} := Fintype.ofFinite _
  apply pi_isPGroup (fun q : {q : Primes G // (q : ℕ) = p} => Fiber G q.1)
  intro q
  letI : Fintype (Sylow (q.1 : ℕ) G) := Fintype.ofFinite _
  apply pi_isPGroup (fun S : Sylow (q.1 : ℕ) G => S)
  intro S
  simpa only [q.2] using S.isPGroup'

theorem complement_coprime : Nat.Coprime (Nat.card (Complement p G)) p := by
  letI : Fintype {q : Primes G // (q : ℕ) ≠ p} := Fintype.ofFinite _
  rw [Nat.card_pi]
  apply Nat.Coprime.prod_left
  intro q _
  letI : Fact (Nat.Prime (q.1 : ℕ)) := ⟨Nat.prime_of_mem_primeFactors q.1.2⟩
  letI : Fintype (Sylow (q.1 : ℕ) G) := Fintype.ofFinite _
  rw [Nat.card_pi]
  apply Nat.Coprime.prod_left
  intro S _
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp S.isPGroup'
  change Nat.Coprime (Nat.card (S : Subgroup G)) p
  rw [hn]
  exact ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors q.1.2)
    (Fact.out : p.Prime)).mpr q.2).pow_left n

theorem factors_coprime :
    Nat.Coprime (Nat.card (PrimePart p G)) (Nat.card (Complement p G)) := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (primePart_isPGroup p G)
  rw [hn]
  exact (complement_coprime p G).symm.pow_left n

theorem complement_nilpotent : Group.IsNilpotent (Complement p G) := by
  apply Group.nilpotent_of_surjective
    ((MonoidHom.snd _ _).comp (equiv p G).toMonoidHom)
  intro b
  exact ⟨(equiv p G).symm (1, b), congrArg Prod.snd ((equiv p G).apply_symm_apply _)⟩

theorem card_eq : Nat.card G = Nat.card (PrimePart p G) * Nat.card (Complement p G) :=
  (Nat.card_congr (equiv p G).toEquiv).trans (Nat.card_prod _ _)

theorem complement_card_lt (hdiv : p ∣ Nat.card G) :
    Nat.card (Complement p G) < Nat.card G := by
  have hnot : ¬ p ∣ Nat.card (Complement p G) :=
    (Fact.out : p.Prime).coprime_iff_not_dvd.mp (complement_coprime p G).symm
  have hpdiv : p ∣ Nat.card (PrimePart p G) :=
    ((Fact.out : p.Prime).dvd_mul.mp (by rwa [card_eq p G] at hdiv)).resolve_right hnot
  have hleft : 1 < Nat.card (PrimePart p G) :=
    lt_of_lt_of_le (Fact.out : p.Prime).one_lt (Nat.le_of_dvd Nat.card_pos hpdiv)
  rw [card_eq p G]
  exact lt_mul_of_one_lt_left Nat.card_pos hleft

end SymmetricSubgroupAsymptotics.NilpotentPrimeFactorSplit
