import SymmetricSubgroupAsymptotics.PrimeRelativeRadicalFiniteGenerators

/-! Explicit words identify a relative radical with an already certified
normal subgroup. Powers use the original normal generators; mixed
commutators and conjugations use the whole original ambient group.
There is no numerical rank, normal-list completeness, or p-group premise. -/
set_option autoImplicit false
open scoped commutatorElement

namespace SymmetricSubgroupAsymptotics

inductive PrimeRelativeRadicalWord (ι κ : Type*) where
  | one : PrimeRelativeRadicalWord ι κ
  | power : κ → PrimeRelativeRadicalWord ι κ
  | mixed : κ → ι → PrimeRelativeRadicalWord ι κ
  | mul : PrimeRelativeRadicalWord ι κ → PrimeRelativeRadicalWord ι κ →
      PrimeRelativeRadicalWord ι κ
  | inv : PrimeRelativeRadicalWord ι κ → PrimeRelativeRadicalWord ι κ
  | conj : ι → PrimeRelativeRadicalWord ι κ → PrimeRelativeRadicalWord ι κ
  | conjInv : ι → PrimeRelativeRadicalWord ι κ → PrimeRelativeRadicalWord ι κ

namespace PrimeRelativeRadicalWord

variable {ι κ G H : Type*} [Group G] [Group H]

def eval (p : ℕ) : PrimeRelativeRadicalWord ι κ → (ι → G) → (κ → G) → G
  | .one, _, _ => 1
  | .power j, _, n => n j ^ p
  | .mixed j i, a, n => ⁅n j, a i⁆
  | .mul u v, a, n => u.eval p a n * v.eval p a n
  | .inv u, a, n => (u.eval p a n)⁻¹
  | .conj i u, a, n => a i * u.eval p a n * (a i)⁻¹
  | .conjInv i u, a, n => (a i)⁻¹ * u.eval p a n * a i

theorem eval_mem (p : ℕ) [Fact p.Prime] (N : Subgroup G) [N.Normal]
    (a : ι → G) (n : κ → G) (hn : ∀ j, n j ∈ N)
    (w : PrimeRelativeRadicalWord ι κ) : w.eval p a n ∈ primeRelativeRadical p N := by
  induction w with
  | one => exact (primeRelativeRadical p N).one_mem
  | power j => exact pow_mem_primeRelativeRadical p N ⟨n j, hn j⟩
  | mixed j i => exact commutator_mem_primeRelativeRadical p N ⟨n j, hn j⟩ (a i)
  | mul u v hu hv => exact (primeRelativeRadical p N).mul_mem hu hv
  | inv u hu => exact (primeRelativeRadical p N).inv_mem hu
  | conj i u hu => exact Subgroup.Normal.conj_mem inferInstance _ hu (a i)
  | conjInv i u hu =>
      simpa only [eval, inv_inv] using
        (Subgroup.Normal.conj_mem (inferInstance : (primeRelativeRadical p N).Normal)
          (u.eval p a n) hu (a i)⁻¹)

theorem map_eval (p : ℕ) (f : G →* H) (w : PrimeRelativeRadicalWord ι κ)
    (a : ι → G) (n : κ → G) :
    f (w.eval p a n) = w.eval p (fun i => f (a i)) (fun j => f (n j)) := by
  induction w <;>
    simp_all only [eval, map_one, map_mul, map_inv, map_pow, map_commutatorElement]

end PrimeRelativeRadicalWord

noncomputable section
variable (p : ℕ) [Fact p.Prime] {G H ι κ τ : Type*} [Group G] [Group H]

/-- A normal target is the exact radical when it contains the finite
power/mixed tests and its generators have explicit radical words. -/
theorem primeRelativeRadical_eq_of_generator_words
    (N R : Subgroup G) [N.Normal] [R.Normal]
    (ambient : ι → G) (hambient : Subgroup.closure (Set.range ambient) = ⊤)
    (normalGenerators : κ → G)
    (hn : Subgroup.closure (Set.range normalGenerators) = N)
    (radicalGenerators : τ → G)
    (hr : Subgroup.closure (Set.range radicalGenerators) = R)
    (words : τ → PrimeRelativeRadicalWord ι κ)
    (hwords : ∀ j, (words j).eval p ambient normalGenerators = radicalGenerators j)
    (hpowers : ∀ j, normalGenerators j ^ p ∈ R)
    (hmixed : ∀ j i, ⁅normalGenerators j, ambient i⁆ ∈ R) :
    primeRelativeRadical p N = R := by
  apply le_antisymm
  · exact primeRelativeRadical_le_of_finite_generator_tests p N
      ambient hambient normalGenerators hn R hpowers hmixed
  · rw [← hr]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j, rfl⟩
    rw [← hwords j]
    apply PrimeRelativeRadicalWord.eval_mem p N ambient normalGenerators
    intro k
    rw [← hn]
    exact Subgroup.subset_closure (Set.mem_range_self k)

/-- Transport preserves the whole ambient conjugation, including a second
application of the relative radical. -/
theorem primeRelativeRadical_map_equiv (e : G ≃* H) (N : Subgroup G) [N.Normal]
    [hM : (N.map e.toMonoidHom).Normal] :
    (primeRelativeRadical p N).map e.toMonoidHom =
      primeRelativeRadical p (N.map e.toMonoidHom) := by
  rw [primeRelativeRadical_eq_powerCommutator, primeRelativeRadical_eq_powerCommutator]
  change (Subgroup.closure (Set.range (fun n : N => (n : G) ^ p)) ⊔
      ⁅N, (⊤ : Subgroup G)⁆).map e.toMonoidHom =
    Subgroup.closure (Set.range (fun n : N.map e.toMonoidHom => (n : H) ^ p)) ⊔
      ⁅N.map e.toMonoidHom, (⊤ : Subgroup H)⁆
  rw [Subgroup.map_sup, Subgroup.map_commutator,
    Subgroup.map_top_of_surjective _ e.surjective, MonoidHom.map_closure]
  congr 2
  ext x
  constructor
  · rintro ⟨_, ⟨n, rfl⟩, rfl⟩
    exact ⟨⟨e (n : G), ⟨n, n.2, rfl⟩⟩, (map_pow e (n : G) p).symm⟩
  · rintro ⟨n, rfl⟩
    obtain ⟨g, hg, he⟩ := n.2
    refine ⟨g ^ p, ⟨⟨g, hg⟩, rfl⟩, ?_⟩
    exact (map_pow e g p).trans (congrArg (fun y => y ^ p) he)

theorem primeRelativeHead_eq_of_radical_card [Finite G]
    (N R : Subgroup G) [N.Normal] (d : ℕ)
    (hradical : primeRelativeRadical p N = R)
    (hcard : Nat.card N = p ^ d * Nat.card R) :
    Module.finrank (ZMod p) (primeRelativeCharacters p N) = d := by
  have h := primeRelativeRadical_card_factorization p N
  rw [hradical] at h
  apply Nat.pow_right_injective (Fact.out : p.Prime).one_lt
  exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := R)) (h.symm.trans hcard)

theorem primeRelativeHead_eq_of_subgroup_eq (N R : Subgroup G) [N.Normal] [R.Normal]
    (h : N = R) :
    Module.finrank (ZMod p) (primeRelativeCharacters p N) =
      Module.finrank (ZMod p) (primeRelativeCharacters p R) := by
  subst R
  rfl

end
end SymmetricSubgroupAsymptotics
