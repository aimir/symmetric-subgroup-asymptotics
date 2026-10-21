import SymmetricSubgroupAsymptotics.CFSGSylowNormalizerGeneration
import Mathlib.Data.Nat.Find

/-! Actual Sylow witnesses and their canonical prime. The property is
transported through the original isomorphism, including both the actual
normalizer and the displayed conjugating element. No simple-group leaf is
asserted without its witnesses. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReduction

def GoodSylowPrime (G : Type*) [Group G] (p : ℕ) : Prop :=
  p.Prime ∧ ∃ (P : Sylow p G) (g : G),
    IsSolvable (Subgroup.normalizer (P : Set G)) ∧
      Subgroup.closure ((P : Set G) ∪
        (P : Subgroup G).map (MulAut.conj g).toMonoidHom) = ⊤

theorem two_conjugates_generate_map {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (P : Subgroup G) (g : G)
    (hgen : Subgroup.closure ((P : Set G) ∪ P.map (MulAut.conj g).toMonoidHom) = ⊤) :
    Subgroup.closure (((P.map e.toMonoidHom) : Set H) ∪
      (P.map e.toMonoidHom).map (MulAut.conj (e g)).toMonoidHom) = ⊤ := by
  let K := Subgroup.closure (((P.map e.toMonoidHom) : Set H) ∪
    (P.map e.toMonoidHom).map (MulAut.conj (e g)).toMonoidHom)
  have hP : P ≤ K.comap e.toMonoidHom := by
    intro x hx
    exact Subgroup.subset_closure (Or.inl ⟨x, hx, rfl⟩)
  have hC : P.map (MulAut.conj g).toMonoidHom ≤ K.comap e.toMonoidHom := by
    rintro _ ⟨x, hx, rfl⟩
    change e (g * x * g⁻¹) ∈ K
    rw [e.map_mul, e.map_mul, e.map_inv]
    exact Subgroup.subset_closure (Or.inr ⟨e x, ⟨x, hx, rfl⟩, rfl⟩)
  have hle := (Subgroup.closure_le (K.comap e.toMonoidHom)).mpr (Set.union_subset hP hC)
  rw [hgen] at hle
  apply top_unique
  intro y _
  obtain ⟨x, rfl⟩ := e.surjective y
  exact hle (Subgroup.mem_top x)

theorem goodSylowPrime_map {G H : Type*} [Group G] [Group H] [Finite G]
    (e : G ≃* H) {p : ℕ} (hp : GoodSylowPrime G p) : GoodSylowPrime H p := by
  obtain ⟨hprime, P, g, hsol, hgen⟩ := hp
  letI goodSylowPrime_map_prime : Fact p.Prime := ⟨hprime⟩
  let Q : Sylow p H := P.mapSurjective (f := e.toMonoidHom) e.surjective
  refine ⟨hprime, Q, e g, ?_, ?_⟩
  · let N := Subgroup.normalizer (P : Set G)
    letI goodSylowPrime_map_normalizer : IsSolvable N := hsol
    let a := N.equivMapOfInjective e.toMonoidHom e.injective
    have hm : IsSolvable (N.map e.toMonoidHom) :=
      solvable_of_solvable_injective (f := a.symm.toMonoidHom) a.symm.injective
    change IsSolvable (Subgroup.normalizer
      (((P : Subgroup G).map e.toMonoidHom) : Set H))
    rw [← Subgroup.map_equiv_normalizer_eq]
    exact hm
  · exact two_conjugates_generate_map e (P : Subgroup G) g hgen

theorem goodSylowPrime_iff {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    (e : G ≃* H) (p : ℕ) : GoodSylowPrime G p ↔ GoodSylowPrime H p :=
  ⟨goodSylowPrime_map e, goodSylowPrime_map e.symm⟩

def leastGoodPrime (G : Type*) [Group G] (h : ∃ p, GoodSylowPrime G p) : ℕ := Nat.find h

theorem leastGoodPrime_good (G : Type*) [Group G] (h : ∃ p, GoodSylowPrime G p) :
    GoodSylowPrime G (leastGoodPrime G h) := Nat.find_spec h

theorem leastGoodPrime_congr {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    (e : G ≃* H) (hG : ∃ p, GoodSylowPrime G p) (hH : ∃ p, GoodSylowPrime H p) :
    leastGoodPrime G hG = leastGoodPrime H hH := by
  exact Nat.find_congr' (fun {p} => goodSylowPrime_iff e p)

end SymmetricSubgroupAsymptotics.CFSGReduction
