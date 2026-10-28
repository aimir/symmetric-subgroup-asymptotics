import SymmetricSubgroupAsymptotics.ExtendedCatalogueNonaffinePrimitiveRank
import SymmetricSubgroupAsymptotics.CFSGSimpleAutomorphismPolylogBudget
import SymmetricSubgroupAsymptotics.CFSGUniformOuterLogBudget

/-! Uniform finite-menu simple-factor budgets for the actual extended
classification target. Only the chosen actual finite model is declared
finite, by transport from D.Simple. No order formula, recognition, outer
callback, or uniform model-finiteness input is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.ExtendedCatalogueFiniteSimpleBudgets
open PrimitiveSocleRawStructure CFSGReduction
open CFSGNonaffinePrimitivePolylogRank
open PrimitiveSocleLargeOneFactorOrdinaryCFSGReduction (RemainingModel)

abbrev FiniteIndex := Option (Option CFSG.Sporadic)
abbrev finiteModel := CFSGAxiomMonsterY443FiniteBudgets.finiteModel

local instance : Fintype FiniteIndex := Fintype.ofFinite _

private theorem finite_simple_rank {G X : Type} [Group G] [Finite G] [Finite X]
    [MulAction G X] (D : NonaffineData G X) (i : FiniteIndex)
    (e : D.Simple ≃* finiteModel i) :
    MarkedC4.genRank D.Simple ≤ CFSGGeneration.familyGenerationDegree finiteModel := by
  obtain ⟨S,hS,hcard⟩ := CFSGGeneration.family_generators_of_mulEquiv finiteModel i e
  exact (MarkedC4.genRank_le hS).trans hcard

private theorem remaining_finite_witness {G X : Type} [Group G] [Finite G] [Finite X]
    [MulAction G X] (D : NonaffineData G X) (i : CFSG.Index) (hi : RemainingModel i)
    (e : D.Simple ≃* i.Model) :
    ∃ j : FiniteIndex, Nonempty (D.Simple ≃* finiteModel j) := by
  cases i <;> try { exact hi.elim }
  case tits => exact ⟨some none,⟨e⟩⟩
  case sporadic s => exact ⟨some (some s),⟨e⟩⟩

/-- The actual factor is either in the proved infinite-model packet or
is one member of the enlarged literal finite menu. -/
theorem factor_packet_or_finite {G X : Type} [Group G] [Finite G] [Finite X]
    [MulAction G X] (D : NonaffineData G X)
    (hclass : CFSGCatalogueWithAxiomMonster.Classification) :
    (∀ ell, LeastProperIndex D.Simple ell → ell^2 < Nat.card D.Simple ∧
      SufficientOuterOrderBudget ell (Nat.card (Outer D.Simple))) ∨
      ∃ i : FiniteIndex, Nonempty (D.Simple ≃* finiteModel i) := by
  obtain ⟨i,e⟩ := CFSGCatalogueWithAxiomMonster.modelWitness hclass D.Simple
  cases i with
  | inr u => exact Or.inr ⟨none,⟨e⟩⟩
  | inl i =>
    let e0 : D.Simple ≃* i.val.Model := e
    letI : Finite i.val.Model := Finite.of_equiv D.Simple e0.toEquiv
    letI : IsSimpleGroup i.val.Model := e0.symm.isSimpleGroup
    have hn : ¬IsMulCommutative i.val.Model :=
      fun hc => D.noncommutative ((isMulCommutative_congr e0).mpr hc)
    rcases CFSGSimpleIndexPacketOrTitsSporadic.model_packet_or_remaining i.val hn with hp | hi
    · exact Or.inl (sufficientSimpleIndexBounds_of_mulEquiv e0 hp)
    · exact Or.inr (remaining_finite_witness D i.val hi e0)

/-- Rank on the SAME simple factor; the actual raw model is absorbed as
one fixed finite-menu member, not identified with the old Monster. -/
theorem exists_uniform_simple_rank_budget (hclass : CFSGCatalogueWithAxiomMonster.Classification) :
    ∃ A : ℕ, ∀ {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
      (D : NonaffineData G X) (ell : ℕ) (hell : LeastProperIndex D.Simple ell),
      MarkedC4.genRank D.Simple ≤ A*(Nat.log 2 ell+2)^2 := by
  let C := CFSGGeneration.familyGenerationDegree finiteModel
  refine ⟨C+32,?_⟩
  intro G X _ _ _ _ D ell hell
  have hbranch : (MarkedC4.genRank D.Simple : ℝ) ≤
      12*(Real.logb 2 (ell : ℝ))^2+1 ∨
      MarkedC4.genRank D.Simple ≤ C := by
    obtain ⟨i,e⟩ := CFSGCatalogueWithAxiomMonster.modelWitness hclass D.Simple
    cases i with
    | inr u => exact Or.inr (finite_simple_rank D none e)
    | inl i =>
      let e0 : D.Simple ≃* i.val.Model := e
      rcases CFSGInfiniteSimplePolylogRank.simple_rank_or_remaining D i.val e0 ell hell with hr | hi
      · exact Or.inl hr
      · obtain ⟨j,⟨ej⟩⟩ := remaining_finite_witness D i.val hi e0
        exact Or.inr (finite_simple_rank D j ej)
  rcases hbranch with hr | hr
  · have h2 : 2 ≤ ell := by
      obtain ⟨H,hH,he⟩ := hell.1
      have hh := H.one_lt_index_of_ne_top hH
      omega
    have hu := logb_le_natLog_add_one ell (by omega)
    have hL : 0 ≤ Real.logb 2 (ell : ℝ) :=
      Real.logb_nonneg (by norm_num) (by exact_mod_cast (show 1 ≤ ell by omega))
    have hs := (sq_le_sq₀ hL (by positivity : (0 : ℝ) ≤ (Nat.log 2 ell : ℝ)+1)).mpr hu
    have hl0 : (0 : ℝ) ≤ Nat.log 2 ell := by positivity
    have hc0 : (0 : ℝ) ≤ C := by positivity
    have hh : (MarkedC4.genRank D.Simple : ℝ) ≤
        ((C+32 : ℕ) : ℝ)*((Nat.log 2 ell+2 : ℕ) : ℝ)^2 := by
      push_cast
      nlinarith only [hr,hs,hu,hl0,hc0,
        mul_nonneg hc0 (sq_nonneg ((Nat.log 2 ell : ℝ)+2))]
    exact_mod_cast hh
  · have hb : C ≤ (C+32)*(Nat.log 2 ell+2)^2 := by
      nlinarith only [Nat.zero_le C,Nat.zero_le (Nat.log 2 ell),
        Nat.zero_le (C*(Nat.log 2 ell)^2),Nat.zero_le (C*Nat.log 2 ell)]
    exact hr.trans hb

theorem exists_uniform_automorphism_budget (hclass : CFSGCatalogueWithAxiomMonster.Classification) :
    ∃ A : ℕ, ∀ {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
      (D : NonaffineData G X) (ell : ℕ) (hell : LeastProperIndex D.Simple ell),
      Nat.card (D.Simple ≃* D.Simple) ≤ Nat.card D.Simple^(A*(Nat.log 2 ell+2)^2) := by
  obtain ⟨A,hA⟩ := exists_uniform_simple_rank_budget hclass
  refine ⟨A,?_⟩
  intro G X _ _ _ _ D ell hell
  obtain ⟨S,hcard,hS⟩ := MarkedC4.genRank_spec (G := D.Simple)
  exact CFSGGeneration.aut_card_le_pow_of_generators S hS (hcard.le.trans (hA D ell hell))

private theorem logb_nat_le_self (n : ℕ) : Real.logb 2 (n : ℝ) ≤ n := by
  by_cases hn : 2 ≤ n
  · have hh := BinaryAffineDominantPrimeSwitchNumerics.logb_nat_le_sub_one n hn
    linarith only [hh]
  · have hh : n=0 ∨ n=1 := by omega
    rcases hh with rfl | rfl <;> norm_num

theorem exists_uniform_outer_log_budget (hclass : CFSGCatalogueWithAxiomMonster.Classification) :
    ∃ B : ℕ, 1 ≤ B ∧ ∀ {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
      (D : NonaffineData G X) (ell : ℕ) (hell : LeastProperIndex D.Simple ell),
      Real.logb 2 (Nat.card (Outer D.Simple) : ℝ) ≤
        (B : ℝ)*Real.logb 2 (ell : ℝ) := by
  let cost : FiniteIndex → ℕ := fun i => Nat.card (Outer (finiteModel i))
  let C := Finset.univ.sup cost
  have hcost (i : FiniteIndex) : cost i ≤ C := Finset.le_sup (Finset.mem_univ i)
  refine ⟨C+6,by omega,?_⟩
  intro G X _ _ _ _ D ell hell
  have hell2 : 2 ≤ ell := by
    obtain ⟨K,hK,he⟩ := hell.1
    have hh := K.one_lt_index_of_ne_top hK
    omega
  have hL : 1 ≤ Real.logb 2 (ell : ℝ) := by
    have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ)<2)
      (by norm_num : (0 : ℝ)<2) (by exact_mod_cast hell2 : (2 : ℝ)≤ell)
    simpa only [Real.logb_self_eq_one (by norm_num : (1 : ℝ)<2)] using hh
  have hlog := logb_nat_le_self (Nat.card (Outer D.Simple))
  rcases factor_packet_or_finite D hclass with hp | ⟨i,⟨e⟩⟩
  · have hout := (hp ell hell).2.log_six
    exact (hlog.trans hout).trans (mul_le_mul_of_nonneg_right
      (by exact_mod_cast (show 6 ≤ C+6 by omega)) (by linarith only [hL]))
  · have hc : Nat.card (Outer D.Simple) ≤ C := by
      rw [outer_card_congr e]
      exact hcost i
    have hcR : (Nat.card (Outer D.Simple) : ℝ) ≤ (C : ℝ) := by exact_mod_cast hc
    have hB : (C : ℝ) ≤ ((C+6 : ℕ) : ℝ) := by exact_mod_cast (show C≤C+6 by omega)
    exact (hlog.trans hcR).trans (hB.trans
      (le_mul_of_one_le_right (Nat.cast_nonneg _) hL))

theorem exists_uniform_degree_outer_log_budget (hclass : CFSGCatalogueWithAxiomMonster.Classification) :
    ∃ B : ℕ, 1 ≤ B ∧ ∀ {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
      (D : NonaffineData G X),
      Real.logb 2 (Nat.card (Outer D.Simple) : ℝ) ≤
        (B : ℝ)*Real.logb 2 (Nat.card X : ℝ) := by
  obtain ⟨B,hB,hbound⟩ := exists_uniform_outer_log_budget hclass
  refine ⟨B,hB,?_⟩
  intro G X _ _ _ _ D
  obtain ⟨ell,hell⟩ := exists_leastProperIndex D.Simple
  have hellpos : 0 < (ell : ℝ) := by
    obtain ⟨K,hK,he⟩ := hell.1
    have hh := K.one_lt_index_of_ne_top hK
    exact_mod_cast (show 0<ell by omega)
  have hdegree : (ell : ℝ) ≤ Nat.card X := by
    exact_mod_cast PrimitiveSocleLeastIndexDegreeComparison.least_index_le_degree D ell hell
  exact (hbound D ell hell).trans (mul_le_mul_of_nonneg_left
    (Real.logb_le_logb_of_le (by norm_num) hellpos hdegree) (Nat.cast_nonneg B))

end SymmetricSubgroupAsymptotics.ExtendedCatalogueFiniteSimpleBudgets
