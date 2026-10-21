import SymmetricSubgroupAsymptotics.CFSGProductSolubleGeneration
import SymmetricSubgroupAsymptotics.CFSGSimpleProductRouting

/-! The simple-to-semisimple soluble-generation step. The actual factors
are retained, and automorphisms may permute isomorphic factors only through
their actual coordinate isomorphisms. The least good prime agrees across
each such isomorphism, so Sylow conjugacy assembles an inner conjugation.
No existence assertion for good primes in simple groups is assumed proved. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Pointwise
namespace SymmetricSubgroupAsymptotics.CFSGReduction

def chosenGoodSylow (G : Type*) [Group G] (h : ∃ p, GoodSylowPrime G p) :
    Sylow (leastGoodPrime G h) G := Classical.choose (leastGoodPrime_good G h).2

def chosenSolubleNormalizer (G : Type*) [Group G] (h : ∃ p, GoodSylowPrime G p) :
    Subgroup G := Subgroup.normalizer (chosenGoodSylow G h : Set G)

theorem chosenSolubleNormalizer_soluble (G : Type*) [Group G]
    (h : ∃ p, GoodSylowPrime G p) : IsSolvable (chosenSolubleNormalizer G h) := by
  obtain ⟨g, hsol, _⟩ := Classical.choose_spec (leastGoodPrime_good G h).2
  exact hsol

theorem chosenSolubleNormalizer_self_normalizing (G : Type*) [Group G] [Finite G]
    (h : ∃ p, GoodSylowPrime G p) :
    Subgroup.normalizer (chosenSolubleNormalizer G h : Set G) = chosenSolubleNormalizer G h := by
  letI chosenNormalizer_self_prime : Fact (leastGoodPrime G h).Prime :=
    ⟨(leastGoodPrime_good G h).1⟩
  exact sylow_normalizer_self_normalizing (chosenGoodSylow G h)

theorem chosenSolubleNormalizer_two_conjugates (G : Type*) [Group G]
    (h : ∃ p, GoodSylowPrime G p) :
    ∃ g : G, Subgroup.closure (((chosenSolubleNormalizer G h) : Set G) ∪
      (chosenSolubleNormalizer G h).map (MulAut.conj g).toMonoidHom) = ⊤ := by
  obtain ⟨g, _, hgen⟩ := Classical.choose_spec (leastGoodPrime_good G h).2
  refine ⟨g, top_unique ?_⟩
  rw [← hgen]
  apply Subgroup.closure_mono
  exact Set.union_subset_union Subgroup.le_normalizer
    (Subgroup.map_mono Subgroup.le_normalizer)

theorem sylow_normalizers_conjugate_across {G H : Type*} [Group G] [Group H]
    [Finite G] [Finite H] (e : G ≃* H) {p q : ℕ} [Fact p.Prime]
    (hpq : p = q) (P : Sylow p G) (Q : Sylow q H) :
    ∃ g : H, (Subgroup.normalizer (P : Set G)).map e.toMonoidHom =
      (Subgroup.normalizer (Q : Set H)).map (MulAut.conj g).toMonoidHom := by
  subst q
  let R : Sylow p H := P.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H Q R
  have hsub : (R : Subgroup H) = (Q : Subgroup H).map (MulAut.conj g).toMonoidHom := by
    have h := congrArg (fun A : Sylow p H => (A : Subgroup H)) hg
    simpa only [Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def] using h.symm
  refine ⟨g, ?_⟩
  calc
    _ = Subgroup.normalizer (((P : Subgroup G).map e.toMonoidHom) : Set H) :=
      Subgroup.map_equiv_normalizer_eq (P : Subgroup G) e
    _ = Subgroup.normalizer (((Q : Subgroup H).map (MulAut.conj g).toMonoidHom) : Set H) :=
      congrArg (fun A : Subgroup H => Subgroup.normalizer (A : Set H)) hsub
    _ = _ := (Subgroup.map_equiv_normalizer_eq (Q : Subgroup H) (MulAut.conj g)).symm

theorem chosenSolubleNormalizer_isomorphism_conjugate {G H : Type*}
    [Group G] [Group H] [Finite G] [Finite H] (e : G ≃* H)
    (hG : ∃ p, GoodSylowPrime G p) (hH : ∃ p, GoodSylowPrime H p) :
    ∃ g : H, (chosenSolubleNormalizer G hG).map e.toMonoidHom =
      (chosenSolubleNormalizer H hH).map (MulAut.conj g).toMonoidHom := by
  letI chosenNormalizer_across_prime : Fact (leastGoodPrime G hG).Prime :=
    ⟨(leastGoodPrime_good G hG).1⟩
  exact sylow_normalizers_conjugate_across e (leastGoodPrime_congr e hG hH)
    (chosenGoodSylow G hG) (chosenGoodSylow H hH)

theorem product_chosen_normalizer_intravariant {I : Type*} [Fintype I]
    (S : I → Type*) [∀ i, Group (S i)] [∀ i, Finite (S i)]
    (hsimple : ∀ i, IsSimpleGroup (S i)) (hZ : ∀ i, IsCenterless (S i))
    (hgood : ∀ i, ∃ p, GoodSylowPrime (S i) p) :
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

/-- A complete conditional simple-to-semisimple step, with no additional
structural premise: actual good Sylow witnesses on the actual factors
produce one actual soluble self-normalizing intravariant subgroup and one
actual conjugating element generating the full original product. -/
theorem semisimple_soluble_generation {I : Type*} [Fintype I]
    (S : I → Type*) [∀ i, Group (S i)] [∀ i, Finite (S i)]
    (hsimple : ∀ i, IsSimpleGroup (S i)) (hZ : ∀ i, IsCenterless (S i))
    (hgood : ∀ i, ∃ p, GoodSylowPrime (S i) p) :
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

theorem intravariant_map_equiv {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (K : Subgroup G) (hK : Intravariant K) :
    Intravariant (K.map e.toMonoidHom) := by
  intro b
  let a : MulAut G := (e.trans b).trans e.symm
  obtain ⟨g, hg⟩ := hK a
  refine ⟨e g, ?_⟩
  have hleft : (K.map a.toMonoidHom).map e.toMonoidHom =
      (K.map e.toMonoidHom).map b.toMonoidHom := by
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    apply MonoidHom.ext
    intro x
    change e (e.symm (b (e x))) = b (e x)
    exact e.apply_symm_apply _
  have hright : (K.map (MulAut.conj g).toMonoidHom).map e.toMonoidHom =
      (K.map e.toMonoidHom).map (MulAut.conj (e g)).toMonoidHom := by
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    apply MonoidHom.ext
    intro x
    change e (g * x * g⁻¹) = e g * e x * (e g)⁻¹
    rw [e.map_mul, e.map_mul, e.map_inv]
  have h := congrArg (fun L : Subgroup G => L.map e.toMonoidHom) hg
  change (K.map a.toMonoidHom).map e.toMonoidHom =
    (K.map (MulAut.conj g).toMonoidHom).map e.toMonoidHom at h
  rw [hleft, hright] at h
  exact h

/-- Transport the actual product witness into a specified original
semisimple carrier. Every subgroup and both generating conjugates are
mapped through the displayed isomorphism. -/
theorem semisimple_soluble_generation_of_equiv {I : Type*} [Fintype I]
    (S : I → Type*) [∀ i, Group (S i)] [∀ i, Finite (S i)]
    (hsimple : ∀ i, IsSimpleGroup (S i)) (hZ : ∀ i, IsCenterless (S i))
    (hgood : ∀ i, ∃ p, GoodSylowPrime (S i) p)
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

end SymmetricSubgroupAsymptotics.CFSGReduction
