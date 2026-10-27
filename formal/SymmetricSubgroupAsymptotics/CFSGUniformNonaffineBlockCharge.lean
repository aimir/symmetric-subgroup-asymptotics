import SymmetricSubgroupAsymptotics.CFSGSimpleAutomorphismPolylogBudget
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexPacketOrTitsSporadic
import SymmetricSubgroupAsymptotics.OriginalNonaffineBlockSocleOrdinaryCost
import SymmetricSubgroupAsymptotics.FiniteModelPrimitiveOrdinaryBudget

/-! A uniform local ordinary-generation charge from CFSG alone.
The finite Tits/sporadic outer multiplicities are absorbed in one finite
constant; the infinite families use their proved proper-index packets.
The actual source recurrence retains its literal socle and block top.
No Tracey/MN premise, simple two-generation, or finite-model callback.
This is a local helper, not the global weak transitive bound or LMM. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGUniformNonaffineBlockCharge
open PrimitiveSocleRawStructure CFSGReduction
open CFSGNonaffinePrimitivePolylogRank
open PrimitiveSocleLargeOneFactorOrdinaryCFSGReduction

private theorem cardFactors_le_self (N : ℕ) (hN : N ≠ 0) :
    ArithmeticFunction.cardFactors N ≤ N := by
  have hp : 2 ^ ArithmeticFunction.cardFactors N ≤ N := by
    simpa only [ArithmeticFunction.cardFactors_apply,MarkedC4.AbelianSectionSize.omega]
      using MarkedC4.AbelianSectionSize.two_pow_omega_le hN
  exact (Nat.le_of_lt (Nat.lt_two_pow_self (n := ArithmeticFunction.cardFactors N))).trans hp

theorem exists_uniform_outer_prime_budget (hCFSG : CFSG.CFSGClassification) :
    ∃ A : ℕ, ∀ {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
      (D : NonaffineData G X) (ell : ℕ) (_hell : LeastProperIndex D.Simple ell),
      ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple)) ≤ A * (Nat.log 2 ell + 2) := by
  letI : Fintype (Option CFSG.Sporadic) := Fintype.ofFinite _
  let cost : Option CFSG.Sporadic → ℕ := fun i =>
    ArithmeticFunction.cardFactors (Nat.card (Outer (finiteModel i)))
  let C := Finset.univ.sup cost
  have hcost (i : Option CFSG.Sporadic) : cost i ≤ C :=
    Finset.le_sup (Finset.mem_univ i)
  refine ⟨C + 6,?_⟩
  intro G X _ _ _ _ D ell hell
  rcases CFSGSimpleIndexPacketOrTitsSporadic.factor_packet_or_actual_remaining_model D hCFSG with
      hp | ⟨i,hi,⟨e⟩⟩
  · have hout := (hp ell hell).2.log_six
    have hu := logb_le_natLog_add_one ell (by
      obtain ⟨K,hK,he⟩ := hell.1
      have hh := K.one_lt_index_of_ne_top hK
      omega)
    have hcf : (ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple)) : ℝ) ≤
        Nat.card (Outer D.Simple) := by
      exact_mod_cast cardFactors_le_self (Nat.card (Outer D.Simple))
        (Nat.card_pos (α := Outer D.Simple)).ne'
    have hreal : (ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple)) : ℝ) ≤
        (6 : ℝ) * ((Nat.log 2 ell : ℝ) + 2) := by
      linarith only [hcf,hout,hu]
    have hnat : ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple)) ≤
        6 * (Nat.log 2 ell + 2) := by exact_mod_cast hreal
    exact hnat.trans (Nat.mul_le_mul_right _ (by omega))
  · have hm (j : Option CFSG.Sporadic) (ej : D.Simple ≃* finiteModel j) :
        ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple)) ≤
          (C + 6) * (Nat.log 2 ell + 2) := by
      rw [outer_card_congr ej]
      exact (hcost j).trans ((by omega : C ≤ C + 6).trans
        (Nat.le_mul_of_pos_right _ (by omega)))
    cases i <;> try { exact hi.elim }
    case tits => exact hm none e
    case sporadic s => exact hm (some s) e

theorem exists_uniform_socle_charge (hCFSG : CFSG.CFSGClassification) :
    ∃ A : ℕ, ∀ {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
      (D : NonaffineData G X),
      2 * MarkedC4.genRank D.Simple +
        (D.factorCount * ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple)) +
          ArithmeticFunction.cardFactors D.factorCount.factorial) ≤
            A * (Nat.log 2 (Nat.card X) + 2) ^ 2 := by
  obtain ⟨A,hA⟩ := CFSGSimpleAutomorphismPolylogBudget.exists_uniform_simple_rank_budget hCFSG
  obtain ⟨B,hB⟩ := exists_uniform_outer_prime_budget hCFSG
  refine ⟨2 * A + B + 1,?_⟩
  intro G X _ _ _ _ D
  obtain ⟨ell,hell⟩ := exists_leastProperIndex D.Simple
  let l := Nat.log 2 (Nat.card X)
  let u := l + 2
  have he : Nat.log 2 ell ≤ l := Nat.log_mono_right
    (PrimitiveSocleLeastIndexDegreeComparison.least_index_le_degree D ell hell)
  have hs : MarkedC4.genRank D.Simple ≤ A * u ^ 2 :=
    (hA D ell hell).trans (Nat.mul_le_mul_left _
      (Nat.pow_le_pow_left (Nat.add_le_add_right he 2) 2))
  have ho : ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple)) ≤ B * u :=
    (hB D ell hell).trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right he 2))
  have hk : D.factorCount ≤ u :=
    (FiniteModelPrimitiveOrdinaryBudget.factorCount_le_log D).trans (by dsimp only [u,l]; omega)
  have hf : ArithmeticFunction.cardFactors D.factorCount.factorial ≤ u ^ 2 :=
    (FiniteModelPrimitiveOrdinaryBudget.factorial_cardFactors_le_square _).trans
      (Nat.pow_le_pow_left hk 2)
  have hm : D.factorCount * ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple)) ≤
      B * u ^ 2 := by
    exact (Nat.mul_le_mul hk ho).trans_eq (by ring)
  calc
    _ ≤ 2 * (A * u ^ 2) + (B * u ^ 2 + u ^ 2) :=
      Nat.add_le_add (Nat.mul_le_mul_left _ hs) (Nat.add_le_add hm hf)
    _ = (2 * A + B + 1) * u ^ 2 := by ring

theorem exists_uniform_nonaffine_block_cost (hCFSG : CFSG.CFSGClassification) :
    ∃ A : ℕ, ∀ {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
      [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
      (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]
      (D : NonaffineData block.Component block.Fibre) (i : block.Points),
      (MarkedC4.genRank J : ℝ) ≤
        (A : ℝ) * ((Nat.log 2 (Nat.card block.Fibre) + 2 : ℕ) : ℝ) ^ 2 *
          ActualWreathChiefUnitMinimumRate.rate (Nat.card block.Points) +
            MarkedC4.genRank block.Top := by
  obtain ⟨A,hA⟩ := exists_uniform_socle_charge hCFSG
  refine ⟨A,?_⟩
  intro n J _ x₀ block _ D i
  have hsource := OriginalNonaffineBlockSocleOrdinaryCost.source_genRank_le_socle_cost J block D i
  change (MarkedC4.genRank J : ℝ) ≤ 2 * (MarkedC4.genRank D.Simple : ℝ) +
    ((D.factorCount * ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple)) +
      ArithmeticFunction.cardFactors D.factorCount.factorial : ℕ) : ℝ) *
        ActualWreathChiefUnitMinimumRate.rate (Nat.card block.Points) +
          MarkedC4.genRank block.Top at hsource
  have hcharge := hA D
  have ht := block.degrees_ge_two.2
  have hrate := ActualWreathChiefUnitMinimumRate.one_le_rate (Nat.card block.Points) ht
  have hhead : 2 * (MarkedC4.genRank D.Simple : ℝ) ≤
      2 * (MarkedC4.genRank D.Simple : ℝ) *
        ActualWreathChiefUnitMinimumRate.rate (Nat.card block.Points) := by
    exact le_mul_of_one_le_right (by positivity) hrate
  have hchargeR : 2 * (MarkedC4.genRank D.Simple : ℝ) +
      ((D.factorCount * ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple)) +
        ArithmeticFunction.cardFactors D.factorCount.factorial : ℕ) : ℝ) ≤
          (A : ℝ) * ((Nat.log 2 (Nat.card block.Fibre) + 2 : ℕ) : ℝ) ^ 2 := by
    exact_mod_cast hcharge
  have hmul := mul_le_mul_of_nonneg_right hchargeR (by linarith only [hrate] :
    0 ≤ ActualWreathChiefUnitMinimumRate.rate (Nat.card block.Points))
  nlinarith only [hsource,hhead,hmul]

end SymmetricSubgroupAsymptotics.CFSGUniformNonaffineBlockCharge
