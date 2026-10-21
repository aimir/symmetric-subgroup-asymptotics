import SymmetricSubgroupAsymptotics.BinaryDegreeEightProperCoverage
import SymmetricSubgroupAsymptotics.BinaryTransitiveNormalQuarterPlusTwo
import SymmetricSubgroupAsymptotics.PrimeCharacterGenerators

/-! Exact degree-eight RDT5.3 packet. The original Heisenberg quotient
provides four independent scalar characters; complete original action
coverage and sharp proper-normal bounds exclude excessive proper normals
in excess-one sources. No published excess input is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryDegreeEightExcessProfile

open MarkedC4 MarkedC4.RDTExcessStructure RDTDegreeEightExceptionalTransport

/-- The exceptional group's actual elementary quotient has dimension4,
so its original whole group needs at least four normal generators. -/
theorem heisenberg_four_le_normalGen_top :
    4 ≤ normalGen (⊤ : Subgroup (BinaryHeisenberg 2)) := by
  let V := (Fin 2 → ZMod 2) × (Fin 2 → ZMod 2)
  let f : Additive (BinaryHeisenberg 2) →+ V :=
    (BinaryHeisenberg.quotient 2).toAdditiveLeft
  have hf : Function.Surjective f := by
    intro v
    obtain ⟨g, hg⟩ := BinaryHeisenberg.quotient_surjective 2 (Multiplicative.ofAdd v)
    exact ⟨Additive.ofMul g, congrArg Multiplicative.toAdd hg⟩
  let L := primeCharacterPullback 2 (BinaryHeisenberg 2) f
  have hL : Function.Injective L := by
    intro a b hab
    apply LinearMap.ext
    intro v
    obtain ⟨g, rfl⟩ := hf v
    exact congrArg (fun χ : PrimeCharacters 2 (BinaryHeisenberg 2) => χ g) hab
  have hdim : Module.finrank (ZMod 2) V = 4 := by
    simpa only [V] using BinaryHeisenberg.quotient_finrank 2
  have hfour := L.finrank_le_finrank_of_injective hL
  rw [Subspace.dual_finrank_eq, hdim] at hfour
  obtain ⟨S, hS, hgen⟩ := MarkedC4.genRank_spec (G := BinaryHeisenberg 2)
  have hchars := (primeCharacterRank_le_generators 2 S hgen).trans_eq hS
  have hp : IsPGroup 2 (BinaryHeisenberg 2) := IsPGroup.of_card (BinaryHeisenberg.card 2)
  letI : Group.IsNilpotent (BinaryHeisenberg 2) := hp.isNilpotent
  have htop := MarkedC4.genRank_le_normalGen_top (G := BinaryHeisenberg 2)
  omega

/-- Literal group equivalence retains the original whole normal rank. -/
theorem four_le_normalGen_top_of_equiv_heisenberg
    {G : Type} [Group G] [Finite G] (e : G ≃* BinaryHeisenberg 2) :
    4 ≤ normalGen (⊤ : Subgroup G) := by
  have he := normalGen_map_equiv e (⊤ : Subgroup G)
  rw [Subgroup.map_top_of_surjective _ e.surjective] at he
  rw [← he]
  exact heisenberg_four_le_normalGen_top

/-- The sole excessive normals of an original excess-one eight-point
binary group are the original whole group. -/
theorem only_whole_of_excess_one
    (G : Subgroup (Equiv.Perm (Fin 8))) (hG : IsPGroup 2 G)
    (htrans : ∀ x y : Fin 8, ∃ g : G, g.val x = y)
    (hexcess : HasExcess G 8 1)
    (N : Subgroup G) [N.Normal] (hhigh : (8 : ℝ) / 4 < normalGen N) : N = ⊤ := by
  rcases BinaryDegreeEightProperCoverage.proper_normal_bounds_or_heisenberg G hG htrans
    with hb | he
  · by_contra hproper
    have hh := hb N hproper
    norm_num at hhigh
    omega
  · obtain ⟨e⟩ := he
    have hmin := four_le_normalGen_top_of_equiv_heisenberg e
    have hmax := hexcess.2 ⊤ inferInstance
    norm_num at hmax
    omega

/-- The full exact h53 conclusion at the original degree8, independently
of the still open sharp degree16/32/64 frontiers. -/
theorem proposition53_degree_eight
    (G : Subgroup (Equiv.Perm (Fin 8))) (hG : IsPGroup 2 G)
    (htrans : ∀ x y : Fin 8, ∃ g : G, g.val x = y)
    (hhigh : ∃ N : Subgroup G, N.Normal ∧ (8 : ℝ) / 4 < normalGen N) :
    ∃ i : ℕ, (i = 1 ∨ i = 2) ∧ HasExcess G 8 i ∧ 8 ≤ 32 ∧
      (i = 1 → ∀ N : Subgroup G, N.Normal → (8 : ℝ) / 4 < normalGen N → N = ⊤) ∧
      (i = 2 → 8 = 8 ∨ 8 = 16 ∨ 8 = 32) := by
  letI : MulAction.IsPretransitive G (Fin 8) := ⟨htrans⟩
  have hall (N : Subgroup G) [N.Normal] : normalGen N ≤ 4 := by
    simpa only [Nat.card_fin] using twoGroup_transitive_normalGen_le_quarter_add_two G hG N
  by_cases hfour : ∃ N : Subgroup G, N.Normal ∧ normalGen N = 4
  · have hexcess : HasExcess G 8 2 := by
      constructor
      · obtain ⟨N, hN, hval⟩ := hfour
        exact ⟨N, hN, by norm_num [hval]⟩
      · intro N hN
        letI := hN
        norm_num
        exact hall N
    exact ⟨2, Or.inr rfl, hexcess, by decide, by intro h; omega, fun _ => Or.inl rfl⟩
  · have hthree (N : Subgroup G) [N.Normal] : normalGen N ≤ 3 := by
      have hb := hall N
      have hne : normalGen N ≠ 4 := fun he => hfour ⟨N, inferInstance, he⟩
      omega
    have hexcess : HasExcess G 8 1 := by
      constructor
      · obtain ⟨N, hN, hval⟩ := hhigh
        letI := hN
        have hb := hthree N
        norm_num at hval
        have heq : normalGen N = 3 := by omega
        exact ⟨N, hN, by norm_num [heq]⟩
      · intro N hN
        letI := hN
        norm_num
        exact hthree N
    refine ⟨1, Or.inl rfl, hexcess, by decide, ?_, fun _ => Or.inl rfl⟩
    intro _ N hN hval
    letI := hN
    exact only_whole_of_excess_one G hG htrans hexcess N hval

end SymmetricSubgroupAsymptotics.BinaryDegreeEightExcessProfile
