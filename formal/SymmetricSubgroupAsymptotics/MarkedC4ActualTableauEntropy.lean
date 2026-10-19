import SymmetricSubgroupAsymptotics.MarkedC4ActualTableauRowIncidence
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! Exact exponential entropy of the actual fixed-tableau incidence row.
The denominator is the actual recovering-array multiplicity. No subgroup
count, source-column capacity, or entropy estimate is an input. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualTableauEntropy
open ActualSubdirectFiltration ActualEfficientRowIncidence
open ActualPrefixOrders ActualTableauRowIncidence

variable {t : ℕ} (F : Fin t → Type) [∀ i,Group (F i)] [∀ i,Finite (F i)]
  (D : ∀ i,Subgroup (F i)) (T : ∀ i j : Fin t,Subgroup (F j))
local instance : Fintype (TableauFamily F D T) := Fintype.ofFinite _

def rowLog (i : Fin t) : ℝ := Real.logb 2 (∏ j : Fin t,Nat.card (T i j) : ℕ)
def prefixLog (H : Subgroup (∀ i,F i)) (m : ℕ) : ℝ :=
  Real.logb 2 (Nat.card («prefix» F H m))
def entropy (H : TableauFamily F D T) : ℝ :=
  (∑ i : Fin t,rowLog F T i*(normalGen (D i) : ℝ))-
    ∑ i : Fin t,prefixLog F H.val.val i.val*(normalGen (D i) : ℝ)

private theorem two_pow_sum_log {ι : Type} [Fintype ι] (v d : ι → ℕ)
    (hv : ∀ i,0<v i) :
    (2 : ℝ)^(∑ i,Real.logb 2 (v i)*(d i : ℝ))=
      ∏ i,(v i : ℝ)^d i := by
  rw [Real.rpow_sum_of_pos (by norm_num : (0 : ℝ)<2)]
  apply Finset.prod_congr rfl
  intro i _
  rw [Real.rpow_mul_natCast (by norm_num : (0 : ℝ)≤2)]
  rw [Real.rpow_logb (by norm_num : (0 : ℝ)<2) (by norm_num : (2 : ℝ)≠1)
    (show (0 : ℝ)<v i by exact_mod_cast hv i)]

/-- The actual tableau row count is bounded by its exact log-order
entropy, with multiplicity division fully justified. -/
theorem card_le_two_pow_entropy (H : TableauFamily F D T) :
    (Nat.card (TableauFamily F D T) : ℝ)≤(2 : ℝ)^entropy F D T H := by
  let U : ℝ := ∑ i : Fin t,rowLog F T i*(normalGen (D i) : ℝ)
  let V : ℝ := ∑ i : Fin t,prefixLog F H.val.val i.val*(normalGen (D i) : ℝ)
  have hnum : ((∏ i : Fin t,(∏ j : Fin t,Nat.card (T i j))^normalGen (D i) : ℕ) : ℝ)=
      (2 : ℝ)^U := by
    symm
    simpa only [U,rowLog,Nat.cast_prod,Nat.cast_pow] using
      two_pow_sum_log (fun i : Fin t => ∏ j : Fin t,Nat.card (T i j))
        (fun i => normalGen (D i)) (fun i => Finset.prod_pos (fun j _ => Nat.card_pos))
  have hmult : (multiplicity F D H.val : ℝ)=(2 : ℝ)^V := by
    symm
    simpa only [V,prefixLog,ActualPrefixOrders.multiplicity,Nat.cast_prod,Nat.cast_pow] using
      two_pow_sum_log (fun i : Fin t => Nat.card («prefix» F H.val.val i.val))
        (fun i => normalGen (D i)) (fun i => Nat.card_pos)
  have hi : (Nat.card (TableauFamily F D T) : ℝ)*(multiplicity F D H.val : ℝ) ≤
      (∏ i : Fin t,(∏ j : Fin t,Nat.card (T i j))^normalGen (D i) : ℕ) := by
    exact_mod_cast ActualTableauRowIncidence.card_mul_multiplicity_le F D T H
  rw [hmult,hnum] at hi
  have hdiv := (le_div_iff₀ (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ)<2) V)).mpr hi
  rw [← Real.rpow_sub (by norm_num : (0 : ℝ)<2)] at hdiv
  exact hdiv

def layerLog (H : Subgroup (∀ i,F i)) (m : ℕ) : ℝ :=
  if hm : m<t then Real.logb 2 (Nat.card (diagonal F H ⟨m,hm⟩)) else 0

/-- The denominator entropy is exactly the sum of the SAME preceding
diagonal log-orders. This supplies the subtraction in the sharp row. -/
theorem prefixLog_eq_sum (H : Subgroup (∀ i,F i)) (m : ℕ) (hm : m≤t) :
    prefixLog F H m=∑ j ∈ Finset.range m,layerLog F H j := by
  induction m with
  | zero => simp [prefixLog,prefix_zero]
  | succ m ih =>
    let i : Fin t := ⟨m,by omega⟩
    have hc := card_prefix_step F H i
    change Nat.card («prefix» F H (m+1))=_ at hc
    unfold prefixLog
    rw [hc,Nat.cast_mul,Real.logb_mul
      (show (Nat.card (diagonal F H i) : ℝ)≠0 by exact_mod_cast (Nat.card_pos (α := diagonal F H i)).ne')
      (show (Nat.card («prefix» F H m) : ℝ)≠0 by exact_mod_cast (Nat.card_pos (α := «prefix» F H m)).ne')]
    change Real.logb 2 (Nat.card (diagonal F H i))+prefixLog F H m=_
    rw [ih (by omega),Finset.sum_range_succ]
    simp only [layerLog,dif_pos (show m<t by omega)]
    ring

end SymmetricSubgroupAsymptotics.MarkedC4.ActualTableauEntropy
