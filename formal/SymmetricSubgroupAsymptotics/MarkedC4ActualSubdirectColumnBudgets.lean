import SymmetricSubgroupAsymptotics.MarkedC4ActualSubdirectColumnProducts
import Mathlib.Data.Nat.Log

/-! Simultaneous column budgets from the literal prefix filtration.
The generator counts and diagonal orders below are constructed from the
same original subgroup. No column capacity or encoding is an input. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualSubdirectColumnBudgets
open ActualSubdirectColumnProducts

private theorem product_budget {ι : Type} (s : Finset ι) (d o : ι → ℕ)
    (q c : ℕ) (h : 2^c ≤ ∏ i ∈ s,min ((2^q)^(d i)) (o i)) :
    c ≤ ∑ i ∈ s,min (q*d i) (Nat.clog 2 (o i)) := by
  apply (Nat.pow_le_pow_iff_right (by omega : 1<2)).mp
  calc
    2^c ≤ ∏ i ∈ s,min ((2^q)^(d i)) (o i) := h
    _ ≤ ∏ i ∈ s,2^(min (q*d i) (Nat.clog 2 (o i))) := by
      apply Finset.prod_le_prod
      · intro i hi
        exact Nat.zero_le _
      · intro i hi
        by_cases hd : q*d i ≤ Nat.clog 2 (o i)
        · rw [min_eq_left hd]
          exact (min_le_left _ _).trans_eq (pow_mul 2 q (d i)).symm
        · rw [min_eq_right (le_of_not_ge hd)]
          exact (min_le_right _ _).trans (Nat.le_pow_clog (by omega) (o i))
    _ = 2^(∑ i ∈ s,min (q*d i) (Nat.clog 2 (o i))) :=
      Finset.prod_pow_eq_pow_sum _ _ _

variable {t : ℕ} (F : Fin t → Type) [∀ i,Group (F i)] [∀ i,Finite (F i)]
  (H : Subgroup (∀ i,F i))
  (hsurj : ∀ i,Function.Surjective (ActualSubdirectFiltration.coordinate F H i))

/-- The first actual column, retaining both local constraints per layer. -/
theorem first_column_le :
    col (Abelian F H) 0 ≤ ∑ m ∈ Finset.range t,
      min (sets F H hsurj m).card (Nat.clog 2 (layerOrder F H m)) := by
  have h := product_budget (Finset.range t)
    (fun m => (sets F H hsurj m).card) (layerOrder F H) 1
    (col (Abelian F H) 0) (by simpa using first_column_product F H hsurj)
  simpa only [one_mul] using h

/-- The sum of the two actual columns uses exactly the SAME layers and
sets as the first-column bound; neither column is independently maximized. -/
theorem two_columns_le :
    col (Abelian F H) 0+col (Abelian F H) 1 ≤ ∑ m ∈ Finset.range t,
      min (2*(sets F H hsurj m).card) (Nat.clog 2 (layerOrder F H m)) := by
  exact product_budget (Finset.range t)
    (fun m => (sets F H hsurj m).card) (layerOrder F H) 2
    (col (Abelian F H) 0+col (Abelian F H) 1)
    (by simpa using two_columns_product F H hsurj)

end SymmetricSubgroupAsymptotics.MarkedC4.ActualSubdirectColumnBudgets
