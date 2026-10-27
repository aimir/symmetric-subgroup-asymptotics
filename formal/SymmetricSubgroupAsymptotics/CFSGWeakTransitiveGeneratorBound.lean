import SymmetricSubgroupAsymptotics.CFSGPrimitiveSubquadraticCount
import SymmetricSubgroupAsymptotics.CFSGUniformNonaffineBlockCharge
import SymmetricSubgroupAsymptotics.PrimitiveAffineUniformLocalCharge
import SymmetricSubgroupAsymptotics.WeakTransitiveDegreeInduction

/-! A weak uniform-constant ordinary generator bound for all actual
transitive permutation groups, from CFSG and the closed induced-module
chief recurrences. The actual block top receives only strict-smaller
degree induction with this SAME constant. No exact Tracey ceiling,
McIver--Neumann theorem, model callback or bounded-degree census is used.
This auxiliary estimate does not assert LMM or discharge sharp bounds. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGWeakTransitiveGeneratorBound
open PrimitiveSocleRawStructure WeakTransitivePolylogAbsorption
open WeakTransitiveDegreeInduction

theorem exists_uniform_generator_budget (hCFSG : CFSG.CFSGClassification) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, 2 ≤ n →
      ∀ J : Subgroup (Equiv.Perm (Fin n)), MulAction.IsPretransitive J (Fin n) →
        (MarkedC4.genRank J : ℝ) ≤ C * rate n := by
  obtain ⟨P,hP⟩ := CFSGPrimitiveSubquadraticCount.exists_uniform_rank_budget hCFSG
  obtain ⟨B,hB⟩ := CFSGUniformNonaffineBlockCharge.exists_uniform_nonaffine_block_cost hCFSG
  let A := P + B + 1
  have hPA : P ≤ A := by dsimp only [A]; omega
  have hBA : B ≤ A := by dsimp only [A]; omega
  have h1A : 1 ≤ A := by dsimp only [A]; omega
  obtain ⟨K,hK,hscaled⟩ := exists_uniform_scaled_local_budget A
  let C := 4 * K
  have hC : 1 ≤ C := by dsimp only [C]; linarith only [hK]
  refine ⟨C,hC,?_⟩
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn J htrans
    letI := htrans
    letI : Nontrivial (Fin n) := Finite.one_lt_card_iff_nontrivial.mp
      (by simpa only [Nat.card_fin] using (show 1 < n by omega))
    by_cases hp : MulAction.IsPreprimitive J (Fin n)
    · letI := hp
      have hnat : MarkedC4.genRank J ≤ P * (Nat.log 2 n + 2) ^ 2 := by
        simpa only [Nat.card_fin] using hP (G := J) (X := Fin n)
      have hnatA : MarkedC4.genRank J ≤ A * (Nat.log 2 n + 2) ^ 2 :=
        hnat.trans (Nat.mul_le_mul_right _ hPA)
      have hreal : (MarkedC4.genRank J : ℝ) ≤ localCharge A n := by
        dsimp only [localCharge]
        exact_mod_cast hnatA
      exact primitive_step A K hK n hn (hscaled n hn) _ hreal
    · let x₀ : Fin n := ⟨0,by omega⟩
      obtain ⟨block⟩ := originalMinimalBlock_nonempty (A := J) x₀ hp
      letI : Fintype block.Points := Fintype.ofFinite _
      letI : Nontrivial block.Fibre := Finite.one_lt_card_iff_nontrivial.mp
        (by have hh := block.degrees_ge_two.1; omega)
      letI : MulAction.IsPreprimitive block.Component block.Fibre := block.component_preprimitive
      let r := Nat.card block.Fibre
      let t := Nat.card block.Points
      have hr : 2 ≤ r := block.degrees_ge_two.1
      have ht : 2 ≤ t := block.degrees_ge_two.2
      have hbelow : SmallerRankBound C n := by
        intro k hk H hk2 hH
        exact ih k hk hk2 H hH
      letI : MulAction.IsPretransitive block.Top block.Points := block.top_pretransitive
      have htop : (MarkedC4.genRank block.Top : ℝ) ≤ C * rate t :=
        rank_of_faithful_transitive_action C n hbelow block.Top block.Points ht
          (by simpa only [Nat.card_fin] using block.degrees_lt.2)
      have hrate : 0 ≤ ActualWreathChiefUnitMinimumRate.rate t :=
        (by norm_num : (0 : ℝ) ≤ 1).trans (ActualWreathChiefUnitMinimumRate.one_le_rate t ht)
      have hsource : (MarkedC4.genRank J : ℝ) ≤
          localCharge A r * ActualWreathChiefUnitMinimumRate.rate t +
            MarkedC4.genRank block.Top := by
        obtain ⟨D | Q⟩ := publishedONanScottStructure block.Component block.Fibre
        · have hh := hB J block D block.base
          have hlocal : (B : ℝ) * ((Nat.log 2 r + 2 : ℕ) : ℝ) ^ 2 ≤ localCharge A r := by
            exact mul_le_mul_of_nonneg_right (by exact_mod_cast hBA) (sq_nonneg _)
          exact hh.trans (add_le_add (mul_le_mul_of_nonneg_right hlocal hrate) le_rfl)
        · have hh := PrimitiveAffineUniformLocalCharge.original_block_cost J block Q block.base
          have hlocal : (((Nat.log 2 r + 2 : ℕ) : ℝ) ^ 2) ≤ localCharge A r := by
            have hA : (1 : ℝ) ≤ A := by exact_mod_cast h1A
            exact le_mul_of_one_le_left (sq_nonneg _) hA
          exact hh.trans (add_le_add (mul_le_mul_of_nonneg_right hlocal hrate) le_rfl)
      have hproduct : r * t = n := by simpa only [Nat.card_fin] using block.degree_product
      have hh := block_step (localCharge A r) K C (by dsimp only [localCharge]; positivity)
        hK (by dsimp only [C]; exact le_rfl) r t hr ht (hscaled r hr)
        (MarkedC4.genRank J : ℝ) (MarkedC4.genRank block.Top : ℝ) hsource htop
      simpa only [hproduct] using hh

theorem exists_uniform_generating_finsets (hCFSG : CFSG.CFSGClassification) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, 2 ≤ n →
      ∀ J : Subgroup (Equiv.Perm (Fin n)), MulAction.IsPretransitive J (Fin n) →
        ∃ S : Finset J, Subgroup.closure (S : Set J) = ⊤ ∧
          (S.card : ℝ) ≤ C * ((n : ℝ) / Real.sqrt (Real.logb 2 (n : ℝ))) := by
  obtain ⟨C,hC,hbound⟩ := exists_uniform_generator_budget hCFSG
  refine ⟨C,hC,?_⟩
  intro n hn J ht
  obtain ⟨S,hcard,hgen⟩ := MarkedC4.genRank_spec (G := J)
  have hc : (S.card : ℝ) ≤ MarkedC4.genRank J := by exact_mod_cast hcard.le
  exact ⟨S,hgen,hc.trans (hbound n hn J ht)⟩

end SymmetricSubgroupAsymptotics.CFSGWeakTransitiveGeneratorBound
