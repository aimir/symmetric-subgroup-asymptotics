import SymmetricSubgroupAsymptotics.ZmudPrimarySocleCharacters
import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas

/-! The finite product over the actual primary types combines their
characters without cancellation: a minimal normal p-factor is killed by
all characters belonging to other primes. Nonabelian minimal normal
subgroups are killed by every factor. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators

namespace SymmetricSubgroupAsymptotics.ZmudAbelianSocleCharacters

variable {G : Type} [Group G] [Finite G]

private theorem prime_exists (N : Subgroup G) (hN : IsMinimalNormalSubgroup N)
    (hcomm : IsMulCommutative N) : ∃ p : ℕ, p.Prime ∧ IsPGroup p N := by
  letI : N.Normal := hN.1
  obtain ⟨C⟩ := elementaryMinimalNormalChart_nonempty N hN.2.1 hcomm (by
    intro K hK hKN
    by_cases hb : K = ⊥
    · exact Or.inl hb
    · exact Or.inr (hN.2.2 K hK hb hKN))
  refine ⟨C.p, C.p_prime, IsPGroup.of_card (n := Module.finrank (ZMod C.p) C.V) ?_⟩
  calc
    Nat.card N = Nat.card (Multiplicative C.V) := Nat.card_congr C.equiv.toEquiv
    _ = Nat.card C.V := Nat.card_congr Multiplicative.toAdd
    _ = C.p ^ Module.finrank (ZMod C.p) C.V := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod C.p), Nat.card_zmod]

private abbrev AbelianMinimal (G : Type) [Group G] :=
  {N : Subgroup G // IsMinimalNormalSubgroup N ∧ IsMulCommutative N}

private instance abelianMinimalFintype : Fintype (AbelianMinimal G) := Fintype.ofFinite _

private def chosenPrime (N : AbelianMinimal G) : ℕ :=
  (prime_exists N.1 N.2.1 N.2.2).choose

private theorem chosenPrime_spec (N : AbelianMinimal G) :
    (chosenPrime N).Prime ∧ IsPGroup (chosenPrime N) N.1 :=
  (prime_exists N.1 N.2.1 N.2.2).choose_spec

private def primes (G : Type) [Group G] [Finite G] : Finset ℕ :=
  Finset.univ.image (chosenPrime (G := G))

private abbrev PrimeIndex (G : Type) [Group G] [Finite G] := {p // p ∈ primes G}

private instance primeIndexFintype : Fintype (PrimeIndex G) := Fintype.ofFinite _

private instance primeIndexFact (q : PrimeIndex G) : Fact q.1.Prime := by
  obtain ⟨N, _, hN⟩ := Finset.mem_image.mp q.2
  exact ⟨hN ▸ (chosenPrime_spec N).1⟩

/-- The full abelian-socle detector tuple, on the actual whole socle. -/
theorem exists_characters {t : ℕ} (ht : SocleNormalGeneratorBound G t) :
    ∃ chi : Fin t → (finiteGroupSocle G →* ℂ),
      (∀ (N : Subgroup G) (hN : IsMinimalNormalSubgroup N), IsMulCommutative N →
        ∃ (i : Fin t) (n : N),
          chi i ⟨n.1, Subgroup.subset_normalClosure ⟨N, hN, n.2⟩⟩ ≠ 1) ∧
      ∀ (N : Subgroup G) (hN : IsMinimalNormalSubgroup N), ¬ IsMulCommutative N →
        ∀ (i : Fin t) (n : N),
          chi i ⟨n.1, Subgroup.subset_normalClosure ⟨N, hN, n.2⟩⟩ = 1 := by
  have hc (q : PrimeIndex G) :=
    ZmudPrimarySocleCharacters.exists_characters (G := G) q.1 (fun _ => True) ht
  choose theta hdetect hother using hc
  let chi : Fin t → (finiteGroupSocle G →* ℂ) := fun i => {
    toFun s := ∏ q : PrimeIndex G, theta q i s
    map_one' := by simp only [map_one, Finset.prod_const_one]
    map_mul' a b := by simp only [map_mul, Finset.prod_mul_distrib] }
  refine ⟨chi, ?_, ?_⟩
  · intro N hN hcomm
    let m : AbelianMinimal G := ⟨N, hN, hcomm⟩
    let q : PrimeIndex G := ⟨chosenPrime m,
      Finset.mem_image.mpr ⟨m, Finset.mem_univ _, rfl⟩⟩
    letI : Fact q.1.Prime := primeIndexFact q
    have hpN : IsPGroup q.1 N := (chosenPrime_spec m).2
    obtain ⟨i, n, hn⟩ := hdetect q N hN trivial hpN
    refine ⟨i, n, ?_⟩
    change (∏ u : PrimeIndex G, theta u i _) ≠ 1
    have heq : (∏ u : PrimeIndex G, theta u i
        ⟨n.1, Subgroup.subset_normalClosure ⟨N, hN, n.2⟩⟩) =
        theta q i ⟨n.1, Subgroup.subset_normalClosure ⟨N, hN, n.2⟩⟩ := by
      apply Finset.prod_eq_single_of_mem q (Finset.mem_univ _)
      intro u _ huq
      have hnot : ¬ IsPGroup u.1 N := by
        intro huN
        have hne : u.1 ≠ q.1 := fun h => huq (Subtype.ext h)
        exact hN.2.1 (disjoint_self.mp
          (IsPGroup.disjoint_of_ne u.1 q.1 hne N N huN hpN))
      exact hother u N hN hnot i n
    rw [heq]
    exact hn
  · intro N hN hnoncomm i n
    change (∏ q : PrimeIndex G, theta q i _) = 1
    apply Finset.prod_eq_one
    intro q _
    apply hother q N hN ?_ i n
    intro hpN
    exact hnoncomm (minimalNormal_isMulCommutative_of_isPGroup q.1 N hN hpN)

end SymmetricSubgroupAsymptotics.ZmudAbelianSocleCharacters
