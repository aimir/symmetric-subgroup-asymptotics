import SymmetricSubgroupAsymptotics.SolubleSylowNormalizerPrime
import SymmetricSubgroupAsymptotics.CFSGSemisimpleSolubleGeneration

/-! Alternate proved semisimple assembler using generating conjugates of
actual soluble Sylow normalizers. The original GoodSylow assembler is
unchanged. Its cross-isomorphism Sylow routing is reused verbatim. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Pointwise
namespace SymmetricSubgroupAsymptotics.SolubleSylowNormalizerGeneration
open CFSGReduction

def chosenGoodSylow (G : Type*) [Group G] (h : ∃ p, SolubleSylowNormalizerPrime G p) :
    Sylow (leastPrime G h) G := Classical.choose (leastPrime_good G h).2

def chosenSolubleNormalizer (G : Type*) [Group G] (h : ∃ p, SolubleSylowNormalizerPrime G p) :
    Subgroup G := Subgroup.normalizer (chosenGoodSylow G h : Set G)

theorem chosenSolubleNormalizer_soluble (G : Type*) [Group G]
    (h : ∃ p, SolubleSylowNormalizerPrime G p) : IsSolvable (chosenSolubleNormalizer G h) := by
  obtain ⟨g, hsol, _⟩ := Classical.choose_spec (leastPrime_good G h).2
  exact hsol

theorem chosenSolubleNormalizer_self_normalizing (G : Type*) [Group G] [Finite G]
    (h : ∃ p, SolubleSylowNormalizerPrime G p) :
    Subgroup.normalizer (chosenSolubleNormalizer G h : Set G) = chosenSolubleNormalizer G h := by
  letI chosenNormalizer_self_prime : Fact (leastPrime G h).Prime :=
    ⟨(leastPrime_good G h).1⟩
  exact sylow_normalizer_self_normalizing (chosenGoodSylow G h)

theorem chosenSolubleNormalizer_two_conjugates (G : Type*) [Group G]
    (h : ∃ p, SolubleSylowNormalizerPrime G p) :
    ∃ g : G, Subgroup.closure (((chosenSolubleNormalizer G h) : Set G) ∪
      (chosenSolubleNormalizer G h).map (MulAut.conj g).toMonoidHom) = ⊤ := by
  obtain ⟨g, _, hgen⟩ := Classical.choose_spec (leastPrime_good G h).2
  exact ⟨g, hgen⟩

theorem chosenSolubleNormalizer_isomorphism_conjugate {G H : Type*}
    [Group G] [Group H] [Finite G] [Finite H] (e : G ≃* H)
    (hG : ∃ p, SolubleSylowNormalizerPrime G p) (hH : ∃ p, SolubleSylowNormalizerPrime H p) :
    ∃ g : H, (chosenSolubleNormalizer G hG).map e.toMonoidHom =
      (chosenSolubleNormalizer H hH).map (MulAut.conj g).toMonoidHom := by
  letI chosenNormalizer_across_prime : Fact (leastPrime G hG).Prime :=
    ⟨(leastPrime_good G hG).1⟩
  exact sylow_normalizers_conjugate_across e (leastPrime_congr e hG hH)
    (chosenGoodSylow G hG) (chosenGoodSylow H hH)

theorem product_chosen_normalizer_intravariant {I : Type*} [Fintype I]
    (S : I → Type*) [∀ i, Group (S i)] [∀ i, Finite (S i)]
    (hsimple : ∀ i, IsSimpleGroup (S i)) (hZ : ∀ i, IsCenterless (S i))
    (hgood : ∀ i, ∃ p, SolubleSylowNormalizerPrime (S i) p) :
    Intravariant (Subgroup.pi Set.univ (fun i => chosenSolubleNormalizer (S i) (hgood i))) := by
  intro e
  obtain ⟨r, hr, a, ha⟩ := simple_product_automorphism_routing S hsimple hZ e
  choose g hg using fun i => chosenSolubleNormalizer_isomorphism_conjugate (a i)
    (hgood (r i)) (hgood i)
  refine ⟨g, ?_⟩
  rw [map_pi_of_routing S _ e r hr.2 a ha]
  rw [map_pi_of_routing S _ (MulAut.conj g) id Function.surjective_id
    (fun i => MulAut.conj (g i)) (by intro x i; rfl)]
  congr 1
  funext i
  exact hg i

/-- Actual soluble Sylow-normalizer conjugate pairs on the actual factors
produce one actual soluble self-normalizing intravariant subgroup and one
actual conjugating element generating the full original product. -/
theorem semisimple_soluble_generation {I : Type*} [Fintype I]
    (S : I → Type*) [∀ i, Group (S i)] [∀ i, Finite (S i)]
    (hsimple : ∀ i, IsSimpleGroup (S i)) (hZ : ∀ i, IsCenterless (S i))
    (hgood : ∀ i, ∃ p, SolubleSylowNormalizerPrime (S i) p) :
    ∃ (H : Subgroup (∀ i, S i)) (g : ∀ i, S i),
      IsSolvable H ∧ Intravariant H ∧ Subgroup.normalizer (H : Set (∀ i, S i)) = H ∧
        Subgroup.closure ((H : Set (∀ i, S i)) ∪ H.map (MulAut.conj g).toMonoidHom) = ⊤ := by
  let H : ∀ i, Subgroup (S i) := fun i => chosenSolubleNormalizer (S i) (hgood i)
  choose g hg using fun i => chosenSolubleNormalizer_two_conjugates (S i) (hgood i)
  exact ⟨Subgroup.pi Set.univ H, g,
    finite_product_soluble S H (fun i => chosenSolubleNormalizer_soluble (S i) (hgood i)),
    product_chosen_normalizer_intravariant S hsimple hZ hgood,
    product_self_normalizing S H
      (fun i => chosenSolubleNormalizer_self_normalizing (S i) (hgood i)),
    product_two_conjugates_generate S H g hg⟩

/-- Transport the actual product witness into a specified original
semisimple carrier. Every subgroup and both generating conjugates are
mapped through the displayed isomorphism. -/
theorem semisimple_soluble_generation_of_equiv {I : Type*} [Fintype I]
    (S : I → Type*) [∀ i, Group (S i)] [∀ i, Finite (S i)]
    (hsimple : ∀ i, IsSimpleGroup (S i)) (hZ : ∀ i, IsCenterless (S i))
    (hgood : ∀ i, ∃ p, SolubleSylowNormalizerPrime (S i) p)
    {G : Type*} [Group G] (e : (∀ i, S i) ≃* G) :
    ∃ (H : Subgroup G) (g : G),
      IsSolvable H ∧ Intravariant H ∧ Subgroup.normalizer (H : Set G) = H ∧
        Subgroup.closure ((H : Set G) ∪ H.map (MulAut.conj g).toMonoidHom) = ⊤ := by
  obtain ⟨H, g, hsol, hinv, hself, hgen⟩ := semisimple_soluble_generation S hsimple hZ hgood
  letI semisimpleGeneration_originalSoluble : IsSolvable H := hsol
  let a := H.equivMapOfInjective e.toMonoidHom e.injective
  have hmapSol : IsSolvable (H.map e.toMonoidHom) :=
    solvable_of_solvable_injective (f := a.symm.toMonoidHom) a.symm.injective
  refine ⟨H.map e.toMonoidHom, e g, hmapSol, intravariant_map_equiv e H hinv, ?_,
    two_conjugates_generate_map e H g hgen⟩
  rw [← Subgroup.map_equiv_normalizer_eq, hself]

end SymmetricSubgroupAsymptotics.SolubleSylowNormalizerGeneration
