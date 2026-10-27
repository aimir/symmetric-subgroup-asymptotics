import SymmetricSubgroupAsymptotics.CFSGGoodSylowPrime

/-! The normalizer conjugates suffice for Suzuki's induction. This is
weaker than generation by the Sylow conjugates themselves, and retains an
actual Sylow prime so that choices route across isomorphic simple factors. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.SolubleSylowNormalizerGeneration
open CFSGReduction

def SolubleSylowNormalizerPrime (G : Type*) [Group G] (p : ℕ) : Prop :=
  p.Prime ∧ ∃ (P : Sylow p G) (g : G),
    IsSolvable (Subgroup.normalizer (P : Set G)) ∧
      Subgroup.closure (((Subgroup.normalizer (P : Set G)) : Set G) ∪
        (Subgroup.normalizer (P : Set G)).map (MulAut.conj g).toMonoidHom) = ⊤

theorem of_goodSylowPrime {G : Type*} [Group G] {p : ℕ}
    (h : GoodSylowPrime G p) : SolubleSylowNormalizerPrime G p := by
  obtain ⟨hp, P, g, hsol, hgen⟩ := h
  refine ⟨hp, P, g, hsol, top_unique ?_⟩
  rw [← hgen]
  apply Subgroup.closure_mono
  exact Set.union_subset_union Subgroup.le_normalizer
    (Subgroup.map_mono Subgroup.le_normalizer)

theorem map {G H : Type*} [Group G] [Group H] [Finite G]
    (e : G ≃* H) {p : ℕ} (hp : SolubleSylowNormalizerPrime G p) :
    SolubleSylowNormalizerPrime H p := by
  obtain ⟨hprime, P, g, hsol, hgen⟩ := hp
  letI : Fact p.Prime := ⟨hprime⟩
  let Q : Sylow p H := P.mapSurjective (f := e.toMonoidHom) e.surjective
  let N := Subgroup.normalizer (P : Set G)
  have hN : N.map e.toMonoidHom = Subgroup.normalizer (Q : Set H) :=
    Subgroup.map_equiv_normalizer_eq (P : Subgroup G) e
  refine ⟨hprime, Q, e g, ?_, ?_⟩
  · letI : IsSolvable N := hsol
    let a := N.equivMapOfInjective e.toMonoidHom e.injective
    have hm : IsSolvable (N.map e.toMonoidHom) :=
      solvable_of_solvable_injective (f := a.symm.toMonoidHom) a.symm.injective
    rw [hN] at hm
    exact hm
  · have hm := two_conjugates_generate_map e N g hgen
    rw [hN] at hm
    exact hm

theorem iff_of_equiv {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    (e : G ≃* H) (p : ℕ) :
    SolubleSylowNormalizerPrime G p ↔ SolubleSylowNormalizerPrime H p :=
  ⟨map e, map e.symm⟩

def leastPrime (G : Type*) [Group G] (h : ∃ p, SolubleSylowNormalizerPrime G p) : ℕ :=
  Nat.find h

theorem leastPrime_good (G : Type*) [Group G]
    (h : ∃ p, SolubleSylowNormalizerPrime G p) :
    SolubleSylowNormalizerPrime G (leastPrime G h) := Nat.find_spec h

theorem leastPrime_congr {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    (e : G ≃* H) (hG : ∃ p, SolubleSylowNormalizerPrime G p)
    (hH : ∃ p, SolubleSylowNormalizerPrime H p) :
    leastPrime G hG = leastPrime H hH :=
  Nat.find_congr' (fun {p} => iff_of_equiv e p)

end SymmetricSubgroupAsymptotics.SolubleSylowNormalizerGeneration
