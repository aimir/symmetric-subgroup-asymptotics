import SymmetricSubgroupAsymptotics.MarkedC4NilpotentSylowFactors

/-! Split one ACTUAL finite nilpotent group into any selected prime part
and its coprime complement. This is the prime-independent analogue of the
existing binary/odd structural split; no product chart is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGNilpotentPrimeFactors
open MarkedC4.NilpotentSylowFactors
variable (p : ℕ) (G : Type) [Group G] [Finite G] [Group.IsNilpotent G]

abbrev PrimePart := ∀ q : {q : Primes G // (q : ℕ)=p},Fiber G q.1
abbrev RestPart := ∀ q : {q : Primes G // (q : ℕ)≠p},Fiber G q.1

def splitProduct : (∀ q : Primes G,Fiber G q) ≃* PrimePart p G × RestPart p G where
  toEquiv := Equiv.piEquivPiSubtypeProd (fun q : Primes G => (q : ℕ)=p) (Fiber G)
  map_mul' _ _ := rfl

def equiv : G ≃* PrimePart p G × RestPart p G :=
  (Sylow.directProductOfNormal (G := G) (fun {q} [Fact q.Prime] S =>
    Sylow.normal_of_normalizerCondition (Group.normalizerCondition_of_isNilpotent (G := G)) S)).symm.trans
      (splitProduct p G)

private theorem pi_isPGroup {q : ℕ} [Fact q.Prime] {I : Type} [Fintype I]
    (V : I → Type) [∀ i,Group (V i)] [∀ i,Finite (V i)]
    (h : ∀ i,IsPGroup q (V i)) : IsPGroup q (∀ i,V i) := by
  choose n hn using fun i => (IsPGroup.iff_card.mp (h i))
  apply IsPGroup.of_card (n := ∑ i,n i)
  rw [Nat.card_pi]
  simp_rw [hn]
  exact Finset.prod_pow_eq_pow_sum Finset.univ n q

theorem prime_isPGroup [Fact p.Prime] : IsPGroup p (PrimePart p G) := by
  letI : Fintype {q : Primes G // (q : ℕ)=p} := Fintype.ofFinite _
  apply pi_isPGroup (fun q : {q : Primes G // (q : ℕ)=p} => Fiber G q.1)
  intro q
  letI : Fintype (Sylow (q.1 : ℕ) G) := Fintype.ofFinite _
  apply pi_isPGroup (fun S : Sylow (q.1 : ℕ) G => S)
  intro S
  simpa only [q.2] using S.isPGroup'

theorem rest_card_coprime [Fact p.Prime] : Nat.Coprime (Nat.card (RestPart p G)) p := by
  letI : Fintype {q : Primes G // (q : ℕ)≠p} := Fintype.ofFinite _
  rw [Nat.card_pi]
  apply Nat.Coprime.prod_left
  intro q _
  letI : Fact (Nat.Prime (q.1 : ℕ)) := ⟨Nat.prime_of_mem_primeFactors q.1.2⟩
  letI : Fintype (Sylow (q.1 : ℕ) G) := Fintype.ofFinite _
  rw [Nat.card_pi]
  apply Nat.Coprime.prod_left
  intro S _
  obtain ⟨n,hn⟩ := IsPGroup.iff_card.mp S.isPGroup'
  change Nat.Coprime (Nat.card (S : Subgroup G)) p
  rw [hn]
  exact ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors q.1.2)
    (Fact.out : p.Prime)).mpr q.2).pow_left n

theorem factors_coprime [Fact p.Prime] :
    Nat.Coprime (Nat.card (PrimePart p G)) (Nat.card (RestPart p G)) := by
  obtain ⟨n,hn⟩ := IsPGroup.iff_card.mp (prime_isPGroup p G)
  rw [hn]
  exact (rest_card_coprime p G).symm.pow_left n

instance rest_nilpotent : Group.IsNilpotent (RestPart p G) := by
  letI (q : {q : Primes G // (q : ℕ)≠p}) :
      Fact (Nat.Prime (q.1 : ℕ)) := ⟨Nat.prime_of_mem_primeFactors q.1.2⟩
  letI (q : {q : Primes G // (q : ℕ)≠p}) (S : Sylow (q.1 : ℕ) G) :
      Group.IsNilpotent S := S.isPGroup'.isNilpotent
  infer_instance

end SymmetricSubgroupAsymptotics.CFSGNilpotentPrimeFactors
