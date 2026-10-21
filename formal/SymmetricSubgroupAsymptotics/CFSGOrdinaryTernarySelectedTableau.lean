import SymmetricSubgroupAsymptotics.CFSGOrdinaryTableauEnergyCount
import SymmetricSubgroupAsymptotics.CFSGOrdinaryExceptionalDensityEnergy
import SymmetricSubgroupAsymptotics.CFSGOrdinarySelectedTableau
import SymmetricSubgroupAsymptotics.CFSGPrimeOrdinaryFactorProfile

/-! A genuine ternary tableau count from the SAME actual prime-group
factors and original nilpotent subdirect source. Active three-point
diagonals have one fixed density and therefore contribute only across
one density cut. No subgroup-counting assertion is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGOrdinaryTernarySelectedTableau
open MarkedC4 ActualTableauPeeling ActualSelectedOrderPrefix ActualSelectedDensityComparisons
open ActualOrderedSubdirectTransport ActualSelectedTableauPacket CFSGPrimeOrdinaryFactorProfile

variable {I : Type} [Fintype I] [DecidableEq I]
    (k : I → ℕ) (U : ∀ i,Subgroup (Equiv.Perm (Fin (3^(k i)))))
    [∀ i,MulAction.IsPretransitive (U i) (Fin (3^(k i)))]
    (hU : ∀ i,IsPGroup 3 (U i))

include hU

/-- The ternary quadratic coefficient is log₂(3)/27, strictly below1/16.
The bounded-factor self-cost is only linear in the number of factors. -/
theorem selected_tableau_card_le
    (H : Subgroup (∀ i,U i))
    {l : List I}
    (h : Plan (ActualLogPeelingAndSelfCost.density (fun i => U i) H
      (fun i => 3^(k i))) Finset.univ l)
    (hfull : ∀ i,Function.Surjective (ActualTableauPeeling.coordinate (fun i => U i) H i))
    [Group.IsNilpotent H] (B : ℝ)
    (hbounded : ∀ i,Real.logb 2 (Nat.card (U i)) ≤ B) :
    (Nat.card (ActualTableauRowIncidence.TableauFamily
      (orderedFactors (fun i => U i) H (fun i => 3^(k i)) h)
      (diagonals (fun i => U i) H (fun i => 3^(k i)) h)
      (tableau (fun i => U i) H (fun i => 3^(k i)) h)) : ℝ) ≤ 
      (2 : ℝ)^((Real.logb 2 3/27)*(∑ i : I,((3^(k i) : ℕ) : ℝ))^2+
        (l.length : ℝ)*B^2) := by
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let F : I → Type := fun i => U i
  let weight : I → ℕ := fun i => 3^(k i)
  let C : ℝ := Real.logb 2 3/2
  let c : Fin l.length → ℝ := fun i => selectedDensity F H weight h i/C
  let n : Fin l.length → ℝ := fun i => weight (reverseOrder h i)
  let D := diagonals F H weight h
  let P : Fin l.length → Prop := fun i => k (reverseOrder h i)=1 ∧ D i≠⊥
  have hlog3 : 0 < Real.logb 2 3 := Real.logb_pos (by norm_num) (by norm_num)
  have hC : 0 < C := div_pos hlog3 (by norm_num)
  have hw : ∀ i,0 < weight i := fun i => pow_pos (by decide) _
  have horder (i : I) : Real.logb 2 (Nat.card (F i)) ≤ C*weight i := by
    have hh := log_order_le 3 (U i) (hU i)
    norm_num at hh
    simpa [F,C,weight] using hh
  have hcancel (i : Fin l.length) : C*c i=selectedDensity F H weight h i := by
    dsimp [c]
    field_simp [ne_of_gt hC]
  have hc0 (i : Fin l.length) : 0 ≤ c i :=
    div_nonneg (ActualBinaryLogDensityBinding.selectedDensity_nonneg F H weight h i) hC.le
  have hc1 (i : Fin l.length) : c i ≤ 1 :=
    (div_le_one hC).mpr
      (CFSGOrdinarySelectedTableau.selectedDensity_le F H weight h C hw horder i)
  have hn (i : Fin l.length) : 0 ≤ n i := Nat.cast_nonneg _
  have hmono : Monotone c := fun i j hij =>
    div_le_div_of_nonneg_right (selectedDensity_mono F H weight h hij) hC.le
  letI (i : Fin l.length) : (D i).Normal := by
    change (diagonals F H weight h i).Normal
    rw [show diagonals F H weight h i=
      ActualSubdirectFiltration.diagonal (orderedFactors F H weight h)
        (orderedSource F H weight h) i from (diagonal_eq_entry (reverseOrder h) F H i).symm]
    exact ActualSubdirectFiltration.diagonalNormal _ _
      (subdirect (reverseOrder h) F H hfull) i
  have hP (i : Fin l.length) (hi : P i) : c i=2/3 := by
    have hd3 : Nat.card (D i)=3 := by
      apply ternary_active_degree_three_card (U (reverseOrder h i)) (hU _) _ (D i) hi.2
      simp only [Nat.card_fin,hi.1,pow_one]
    have hd := diagonal_log F H weight h hw i
    change Real.logb 2 (Nat.card (D i))=selectedDensity F H weight h i*n i at hd
    have hn3 : n i=3 := by simp only [n,weight,hi.1,pow_one,Nat.cast_ofNat]
    rw [hd3,hn3,←hcancel] at hd
    dsimp [C] at *
    nlinarith
  have hrank (i : Fin l.length) : (normalGen (D i) : ℝ) ≤ (2/9)*n i+
      (if P i then (1/9)*n i else 0) := by
    have ht := ternary_normalGen_real_le (k (reverseOrder h i))
      (U (reverseOrder h i)) (hU _) (by simp only [Nat.card_fin]) (D i)
    simpa only [P,n,weight,Nat.card_fin] using ht
  have henergy := CFSGOrdinaryTableauEnergy.ternary_ranked_energy_le P c n
    (fun i => (normalGen (D i) : ℝ)) hc0 hc1 hn hmono hP (by
      intro i
      have hiR := hrank i
      by_cases hi : P i
      · rw [if_pos hi] at hiR ⊢
        exact hiR
      · rw [if_neg hi] at hiR ⊢
        exact hiR)
  have hcount := CFSGOrdinaryTableauCount.card_le_of_energy
    (orderedFactors F H weight h) D (tableau F H weight h)
    (member F H weight h hfull) c n C B ((2/27)*(∑ i : Fin l.length,n i)^2) hC.le
    (by intro i j hji; rw [hcancel]; exact entry_bound F H weight h hw i j hji)
    (by intro i; rw [hcancel]; exact diagonal_log F H weight h hw i)
    (fun i => hbounded (reverseOrder h i)) henergy
  have hsum : (∑ i : Fin l.length,n i)=∑ i : I,((3^(k i) : ℕ) : ℝ) :=
    (reverseOrder h).sum_comp (fun i : I => (weight i : ℝ))
  rw [hsum] at hcount
  convert hcount using 1  <;> dsimp [C]  <;> ring

end SymmetricSubgroupAsymptotics.CFSGOrdinaryTernarySelectedTableau
