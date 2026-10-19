import SymmetricSubgroupAsymptotics.MarkedC4ActualSubdirectColumnBudgets
import SymmetricSubgroupAsymptotics.MarkedC4ActualNormalGeneratorDensity
import SymmetricSubgroupAsymptotics.MarkedC4CaseIComplete

/-! The Case-I joint splice for the actual retained subdirect source.
Both source capacities are DERIVED from its same diagonal tuple. The only
quarter-rank condition is the indispensable local Case-I/nonexcess condition;
no assertion of quarter rank for arbitrary physical factors is made. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualCaseIColumnBridge
open ActualSubdirectFiltration ActualSubdirectColumnProducts

variable {t : ℕ} (F : Fin t → Type) [∀ i,Group (F i)] [∀ i,Finite (F i)]
  (H : Subgroup (∀ i,F i))
  (hsurj : ∀ i,Function.Surjective (coordinate F H i))

def rankAt (m : ℕ) : ℕ :=
  if hm : m<t then normalGen (diagonal F H ⟨m,hm⟩) else 0

theorem sets_card_le_rankAt (m : ℕ) (hm : m<t) :
    (sets F H hsurj m).card ≤ rankAt F H m := by
  simp only [sets,rankAt,dif_pos hm]
  exact Finset.card_image_le.trans (generators_spec F H hsurj ⟨m,hm⟩).1

include hsurj in
/-- First actual source column, paid by the actual diagonal normal ranks. -/
theorem first_column_le :
    col (Abelian F H) 0 ≤ ∑ m ∈ Finset.range t,rankAt F H m := by
  apply (ActualSubdirectColumnBudgets.first_column_le F H hsurj).trans
  apply Finset.sum_le_sum
  intro m hm
  exact (min_le_left _ _).trans
    (sets_card_le_rankAt F H hsurj m (Finset.mem_range.mp hm))

include hsurj in
/-- The joint capacity retains the SAME local order and rank in each term. -/
theorem two_columns_le :
    col (Abelian F H) 0+col (Abelian F H) 1 ≤
      ∑ m ∈ Finset.range t,
        min (2*rankAt F H m) (Nat.clog 2 (layerOrder F H m)) := by
  apply (ActualSubdirectColumnBudgets.two_columns_le F H hsurj).trans
  apply Finset.sum_le_sum
  intro m hm
  exact min_le_min (Nat.mul_le_mul_left 2
    (sets_card_le_rankAt F H hsurj m (Finset.mem_range.mp hm))) le_rfl

include hsurj in
theorem rankAt_le_order (m : ℕ) (hm : m<t) :
    rankAt F H m ≤ Nat.clog 2 (layerOrder F H m) := by
  letI : (diagonal F H ⟨m,hm⟩).Normal := diagonalNormal F H hsurj ⟨m,hm⟩
  simpa only [rankAt,layerOrder,dif_pos hm] using
    ActualNormalGeneratorDensity.normalGen_le_clog_card (diagonal F H ⟨m,hm⟩)

include hsurj in
/-- The compressed Hall exponent is bounded with the actual source E=H.
The density/order identification and monotone order refer to its actual
tableau; the two source-column inequalities are not supplied as premises. -/
theorem entropy_add_actualHall_le (n c : ℕ → ℝ) {a r : ℝ}
    (ha : 0≤a) (hr : 0≤r)
    (hn : ∀ m<t,0≤n m)
    (hc0 : ∀ m<t,0≤c m) (hc1 : ∀ m<t,c m≤1)
    (hmono : ∀ j m,j≤m → m<t → c j≤c m)
    (horder : ∀ m<t,(Nat.clog 2 (layerOrder F H m) : ℝ)=c m*n m)
    (hnonexcess : ∀ m<t,(rankAt F H m : ℝ)≤n m/4) :
    (∑ m ∈ Finset.range t,∑ j ∈ Finset.range m,
        (c m-c j)*n j*(rankAt F H m : ℝ))+
      psi (a/2+r) (col (Abelian F H) 0)+psi r (col (Abelian F H) 1) ≤
        markedF (a+prefixWeight n t) r := by
  have hf : (col (Abelian F H) 0 : ℝ) ≤
      ∑ m ∈ Finset.range t,(rankAt F H m : ℝ) := by
    exact_mod_cast first_column_le F H hsurj
  have hj : (col (Abelian F H) 0 : ℝ)+(col (Abelian F H) 1 : ℝ) ≤
      ∑ m ∈ Finset.range t,
        min (2*(rankAt F H m : ℝ)) (Nat.clog 2 (layerOrder F H m) : ℝ) := by
    exact_mod_cast two_columns_le F H hsurj
  have hj' : (col (Abelian F H) 0 : ℝ)+(col (Abelian F H) 1 : ℝ) ≤
      ∑ m ∈ Finset.range t,min (2*(rankAt F H m : ℝ)) (c m*n m) := by
    convert hj using 1
    apply Finset.sum_congr rfl
    intro m hm
    rw [horder m (Finset.mem_range.mp hm)]
  have hsecond : (col (Abelian F H) 1 : ℝ)≤col (Abelian F H) 0 := by
    exact_mod_cast col_succ_le (Abelian F H) 0
  have hdensity : ∀ m<t,(rankAt F H m : ℝ)≤c m*n m := by
    intro m hm
    rw [← horder m hm]
    exact_mod_cast rankAt_le_order F H hsurj m hm
  exact caseI_entropy_add_compressedHall_le c n (fun m => (rankAt F H m : ℝ)) t
    ha hr (by positivity) (by positivity) hsecond hf hj' hn hc0 hc1 hmono
    (fun _ _ => Nat.cast_nonneg _) hnonexcess hdensity

end SymmetricSubgroupAsymptotics.MarkedC4.ActualCaseIColumnBridge
