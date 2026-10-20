import SymmetricSubgroupAsymptotics.MarkedC4ActualTableauPeeling
import SymmetricSubgroupAsymptotics.MarkedC4ActualNormalGeneratorDensity
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! Peeling with EXACT real log-orders of actual coordinate images, and
the bounded diagonal self-cost. Exact log peeling avoids any need to identify
a ceiling logarithm with a real logarithm before density subtraction. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualLogPeelingAndSelfCost
open ActualTableauPeeling

variable {I : Type} [Fintype I] [DecidableEq I]
  (F : I → Type) [∀ i,Group (F i)] [∀ i,Finite (F i)]
  (H : Subgroup (∀ i,F i)) (weight : I → ℕ)

def density (i : I) (S : Finset I) : ℝ :=
  Real.logb 2 (Nat.card (entry F H S i))/(weight i : ℝ)

theorem density_mono (i : I) : Monotone (density F H weight i) := by
  intro S U hSU
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Real.logb_le_logb_of_le (by norm_num : (1 : ℝ)<2)
    (show (0 : ℝ)<Nat.card (entry F H S i) by exact_mod_cast Nat.card_pos)
  exact_mod_cast Nat.card_le_card_of_injective _
    (Subgroup.inclusion_injective (entry_mono F H i hSU))

/-- A complete original-factor selection is actually constructed using
the real log-order densities that occur in the incidence exponent. -/
theorem exists_actual_plan (S : Finset I) :
    ∃ l,Plan (density F H weight) S l ∧ l.toFinset=S ∧ l.length=S.card := by
  obtain ⟨l,hl⟩ := ActualTableauPeeling.exists_plan (density F H weight) S
  exact ⟨l,hl,hl.labels,hl.length⟩

/-- Every residual actual entry obeys the selected head's exact density.
This is the local order comparison used in actual tableau entropy. -/
theorem entry_log_le_selected_density {S U : Finset I} {i j : I}
    (hmax : ∀ k∈S,density F H weight k S≤density F H weight i S)
    (hUS : U⊆S) (hj : j∈U) (hw : 0<weight j) :
    Real.logb 2 (Nat.card (entry F H U j))≤
      density F H weight i S*(weight j : ℝ) := by
  have hd := residual_density_le (density_mono F H weight) hmax hUS hj
  exact (div_le_iff₀ (show (0 : ℝ)<weight j by exact_mod_cast hw)).mp hd

section Diagonal
variable {G : Type} [Group G] [Finite G]

/-- The actual normal rank is bounded by the actual real log-order. -/
theorem normalGen_le_real_log (N : Subgroup G) [N.Normal] :
    (normalGen N : ℝ)≤Real.logb 2 (Nat.card N) := by
  apply (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ)<2)).mp
  rw [Real.rpow_logb (by norm_num : (0 : ℝ)<2) (by norm_num : (2 : ℝ)≠1)
    (show (0 : ℝ)<Nat.card N by exact_mod_cast Nat.card_pos),Real.rpow_natCast]
  exact_mod_cast ActualNormalGeneratorDensity.two_pow_normalGen_le_card N

/-- A physical log-order bound pays the diagonal self-cost uniformly. -/
theorem diagonal_self_cost_le (N : Subgroup G) [N.Normal] {B : ℝ}
    (hG : Real.logb 2 (Nat.card G)≤B) :
    Real.logb 2 (Nat.card N)*(normalGen N : ℝ)≤B^2 := by
  have hr := normalGen_le_real_log N
  have hn : Real.logb 2 (Nat.card N)≤B := by
    apply (Real.logb_le_logb_of_le (by norm_num : (1 : ℝ)<2)
      (show (0 : ℝ)<Nat.card N by exact_mod_cast Nat.card_pos) _).trans hG
    exact_mod_cast Nat.card_le_card_of_injective N.subtype Subtype.val_injective
  have hB : 0≤B := (Nat.cast_nonneg (normalGen N)).trans (hr.trans hn)
  have hprod := mul_le_mul hn (hr.trans hn) (Nat.cast_nonneg (normalGen N)) hB
  nlinarith
end Diagonal

/-- Summed self-cost is linear in the number of bounded physical factors;
it does not spend quadratic tableau entropy. -/
theorem total_diagonal_self_cost_le (D : ∀ i,Subgroup (F i))
    [∀ i,(D i).Normal] {B : ℝ}
    (hF : ∀ i,Real.logb 2 (Nat.card (F i))≤B) :
    (∑ i : I,Real.logb 2 (Nat.card (D i))*(normalGen (D i) : ℝ))≤
      (Fintype.card I : ℝ)*B^2 := by
  calc
    _ ≤ ∑ _i : I,B^2 := Finset.sum_le_sum (fun i _ => diagonal_self_cost_le (D i) (hF i))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]

end SymmetricSubgroupAsymptotics.MarkedC4.ActualLogPeelingAndSelfCost
