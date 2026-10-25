import SymmetricSubgroupAsymptotics.ActualWreathPrimitiveSocleOuterOrdinaryCost
import SymmetricSubgroupAsymptotics.OriginalBlockOrdinaryCompressionState
import SymmetricSubgroupAsymptotics.PrimitiveSocleLeastIndexDegreeComparison

/-! Original nonaffine block-component binding. Only strictly-smaller
TRANSITIVE induction is applied: to the genuine simple-factor coset action
and to the genuine original block top. The local homogeneous chart, outer
multiplicity and correlated source remain literal. No scalar-fit hypothesis
or global permutation-generator theorem is supplied. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalNonaffineBlockSocleOrdinaryCost
open PrimitiveSocleRawStructure TraceyStrictlySmallerTransitiveActions
open OriginalBlockOrdinaryCompressionState ActualWreathChiefUnitMinimumRate
open ActualWreathPrimitiveSocleOuterOrdinaryCost

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]

local instance fibreNontrivial : Nontrivial block.Fibre :=
  Finite.one_lt_card_iff_nontrivial.mp (by
    have h := block.degrees_ge_two.1
    omega)
local instance componentPrimitive : MulAction.IsPreprimitive block.Component block.Fibre :=
  block.component_preprimitive

local instance stateComponentAction :
    MulAction (initialState J block).D block.Fibre :=
  inferInstanceAs (MulAction block.Component block.Fibre)
local instance stateComponentFaithful :
    FaithfulSMul (initialState J block).D block.Fibre :=
  inferInstanceAs (FaithfulSMul block.Component block.Fibre)
local instance stateComponentPrimitive :
    MulAction.IsPreprimitive (initialState J block).D block.Fibre :=
  block.component_preprimitive

variable (D : NonaffineData block.Component block.Fibre)

omit [Fintype block.Points] in
private theorem simple_rank_of_smaller (ell : ℕ) (hell : LeastProperIndex D.Simple ell)
    (hbelow : SmallerTransitiveRankBound n) :
    MarkedC4.genRank D.Simple ≤ traceyPermutationGeneratorCeiling ell := by
  have hle := PrimitiveSocleLeastIndexDegreeComparison.least_index_le_degree D ell hell
  have hlt : ell < n := hle.trans_lt (by simpa only [Nat.card_fin] using block.degrees_lt.1)
  exact SimpleLeastIndexStrictOrdinaryGenerators.genRank_le_of_strictly_smaller
    D.Simple n ell hbelow hell hlt

omit [Fintype block.Points] in
private theorem top_rank_of_smaller (hbelow : SmallerTransitiveRankBound n) :
    MarkedC4.genRank block.Top ≤ traceyPermutationGeneratorCeiling (Nat.card block.Points) := by
  letI : MulAction.IsPretransitive block.Top block.Points := block.top_pretransitive
  exact rank_of_faithful_transitive_action n hbelow block.Top block.Points
    block.degrees_ge_two.2 (by simpa only [Nat.card_fin] using block.degrees_lt.2)

/-- The actual original source bound before any scalar fitting. -/
theorem source_genRank_le_socle_cost (i : block.Points) :
    (MarkedC4.genRank J : ℝ) ≤ 2*(MarkedC4.genRank D.Simple : ℝ)+
      (outerMultiplicity (initialState J block) D : ℝ)*rate (Nat.card block.Points)+
        MarkedC4.genRank block.Top := by
  have hI : 2 ≤ Fintype.card block.Points := by
    simpa only [Fintype.card_eq_nat_card] using block.degrees_ge_two.2
  have hh := @genRank_le_twice_simple_add_outer_rate
    block.Top block.Points _ _ _ _ _ (initialState J block) block.Fibre _
    (inferInstanceAs (MulAction block.Component block.Fibre)) D
    (inferInstanceAs (FaithfulSMul block.Component block.Fibre))
    (fibreNontrivial J block) block.component_preprimitive i hI
  simpa only [Fintype.card_eq_nat_card] using hh

/-- Both induction uses are on genuine inherited transitive actions of
strictly smaller degree. The original point count n is retained. -/
theorem genRank_le_strict_coset_cost (i : block.Points) (ell : ℕ)
    (hell : LeastProperIndex D.Simple ell) (hbelow : SmallerTransitiveRankBound n) :
    (MarkedC4.genRank J : ℝ) ≤ 2*(traceyPermutationGeneratorCeiling ell : ℝ)+
      (outerMultiplicity (initialState J block) D : ℝ)*rate (Nat.card block.Points)+
        traceyPermutationGeneratorCeiling (Nat.card block.Points) := by
  have hh := source_genRank_le_socle_cost J block D i
  have hs : (MarkedC4.genRank D.Simple : ℝ) ≤ traceyPermutationGeneratorCeiling ell := by
    exact_mod_cast simple_rank_of_smaller J block D ell hell hbelow
  have ht : (MarkedC4.genRank block.Top : ℝ) ≤
      traceyPermutationGeneratorCeiling (Nat.card block.Points) := by
    exact_mod_cast top_rank_of_smaller J block hbelow
  linarith only [hh,hs,ht]

/-- One-factor local components retain a single simple-factor rank charge. -/
theorem genRank_le_one_factor_strict_coset_cost (i : block.Points) (ell : ℕ)
    (hell : LeastProperIndex D.Simple ell) (hk : D.factorCount = 1)
    (hbelow : SmallerTransitiveRankBound n) :
    (MarkedC4.genRank J : ℝ) ≤ (traceyPermutationGeneratorCeiling ell : ℝ)+
      (outerMultiplicity (initialState J block) D : ℝ)*rate (Nat.card block.Points)+
        traceyPermutationGeneratorCeiling (Nat.card block.Points) := by
  have hI : 2 ≤ Fintype.card block.Points := by
    simpa only [Fintype.card_eq_nat_card] using block.degrees_ge_two.2
  have hh := genRank_le_simple_add_outer_rate_of_one_factor
    (initialState J block) D i hI hk
  simp only [Fintype.card_eq_nat_card] at hh
  change (MarkedC4.genRank J : ℝ) ≤ (MarkedC4.genRank D.Simple : ℝ)+
    (outerMultiplicity (initialState J block) D : ℝ)*rate (Nat.card block.Points)+
      MarkedC4.genRank block.Top at hh
  have hs : (MarkedC4.genRank D.Simple : ℝ) ≤ traceyPermutationGeneratorCeiling ell := by
    exact_mod_cast simple_rank_of_smaller J block D ell hell hbelow
  have ht : (MarkedC4.genRank block.Top : ℝ) ≤
      traceyPermutationGeneratorCeiling (Nat.card block.Points) := by
    exact_mod_cast top_rank_of_smaller J block hbelow
  linarith only [hh,hs,ht]

theorem exists_generating_finset (i : block.Points) (ell : ℕ)
    (hell : LeastProperIndex D.Simple ell) (hbelow : SmallerTransitiveRankBound n) :
    ∃ F : Finset J, Subgroup.closure (F : Set J) = ⊤ ∧
      (F.card : ℝ) ≤ 2*(traceyPermutationGeneratorCeiling ell : ℝ)+
        (outerMultiplicity (initialState J block) D : ℝ)*rate (Nat.card block.Points)+
          traceyPermutationGeneratorCeiling (Nat.card block.Points) := by
  obtain ⟨F,hcard,hgen⟩ := MarkedC4.genRank_spec (G := J)
  have hcardR : (F.card : ℝ) ≤ MarkedC4.genRank J := by exact_mod_cast hcard.le
  exact ⟨F,hgen,hcardR.trans (genRank_le_strict_coset_cost J block D i ell hell hbelow)⟩

end SymmetricSubgroupAsymptotics.OriginalNonaffineBlockSocleOrdinaryCost
