import SymmetricSubgroupAsymptotics.CFSGUniformNonaffineBlockCharge
import SymmetricSubgroupAsymptotics.BinaryAffineDominantPrimeSwitchNumerics

/-! One uniform outer-order logarithm bound from the same actual
simple-factor packet. Finite Tits/sporadic values are absorbed in a
finite natural supremum; no finiteness/model callback is introduced. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGUniformOuterLogBudget
open PrimitiveSocleRawStructure CFSGReduction
open CFSGNonaffinePrimitivePolylogRank
open PrimitiveSocleLargeOneFactorOrdinaryCFSGReduction

private theorem logb_nat_le_self (n : ℕ) : Real.logb 2 (n : ℝ) ≤ n := by
  by_cases hn : 2 ≤ n
  · have hh := BinaryAffineDominantPrimeSwitchNumerics.logb_nat_le_sub_one n hn
    linarith only [hh]
  · have hh : n=0 ∨ n=1 := by omega
    rcases hh with rfl | rfl <;> norm_num

theorem exists_uniform_outer_log_budget (hCFSG : CFSG.CFSGClassification) :
    ∃ B : ℕ, 1 ≤ B ∧ ∀ {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
      (D : NonaffineData G X) (ell : ℕ) (hell : LeastProperIndex D.Simple ell),
      Real.logb 2 (Nat.card (Outer D.Simple) : ℝ) ≤
        (B : ℝ)*Real.logb 2 (ell : ℝ) := by
  letI : Fintype (Option CFSG.Sporadic) := Fintype.ofFinite _
  let cost : Option CFSG.Sporadic → ℕ := fun i => Nat.card (Outer (finiteModel i))
  let C := Finset.univ.sup cost
  have hcost (i : Option CFSG.Sporadic) : cost i ≤ C :=
    Finset.le_sup (Finset.mem_univ i)
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
  rcases CFSGSimpleIndexPacketOrTitsSporadic.factor_packet_or_actual_remaining_model D hCFSG with
      hp | ⟨i,hi,⟨e⟩⟩
  · have hout := (hp ell hell).2.log_six
    exact (hlog.trans hout).trans (mul_le_mul_of_nonneg_right
      (by exact_mod_cast (show 6 ≤ C+6 by omega)) (by linarith only [hL]))
  · have hm (j : Option CFSG.Sporadic) (ej : D.Simple ≃* finiteModel j) :
        Real.logb 2 (Nat.card (Outer D.Simple) : ℝ) ≤
          ((C+6 : ℕ) : ℝ)*Real.logb 2 (ell : ℝ) := by
      have hc : Nat.card (Outer D.Simple) ≤ C := by
        rw [outer_card_congr ej]
        exact hcost j
      have hcR : (Nat.card (Outer D.Simple) : ℝ) ≤ (C : ℝ) := by exact_mod_cast hc
      have hB : (C : ℝ) ≤ ((C+6 : ℕ) : ℝ) := by exact_mod_cast (show C≤C+6 by omega)
      exact (hlog.trans hcR).trans (hB.trans
        (le_mul_of_one_le_right (Nat.cast_nonneg _) hL))
    cases i <;> try { exact hi.elim }
    case tits => exact hm none e
    case sporadic s => exact hm (some s) e

theorem exists_uniform_degree_outer_log_budget (hCFSG : CFSG.CFSGClassification) :
    ∃ B : ℕ, 1 ≤ B ∧ ∀ {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
      (D : NonaffineData G X),
      Real.logb 2 (Nat.card (Outer D.Simple) : ℝ) ≤
        (B : ℝ)*Real.logb 2 (Nat.card X : ℝ) := by
  obtain ⟨B,hB,hbound⟩ := exists_uniform_outer_log_budget hCFSG
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

end SymmetricSubgroupAsymptotics.CFSGUniformOuterLogBudget
