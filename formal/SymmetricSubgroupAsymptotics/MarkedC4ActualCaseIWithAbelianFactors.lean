import SymmetricSubgroupAsymptotics.MarkedC4ActualAbelianFactorSplit

/-! Literal Case-I endpoint with arbitrary abelian quotient factors.
Only nonabelian factors satisfy the actual normal-generator quarter bound;
all abelian factors are constructed into one physical Hall block. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualCaseIWithAbelianFactors
open ActualFullPhysicalWordPeel ActualAbelianFactorSplit

theorem marked_word_card_le {t : ℕ}
    (F : Fin t → Type) [∀ i,Group (F i)] [∀ i,Finite (F i)]
    (weight : Fin t → ℕ) (K : ℕ) (hK : ∀ i,Nat.card (F i)≤K)
    (hw : ∀ i,0<weight i) (hbinary : ∀ i,IsPGroup 2 (F i))
    (hcard : ∀ i,Nat.card (F i)≤2^weight i)
    (hquarter : ∀ (i : Fin t),¬Abelian F i →∀ V : Subgroup (F i),V.Normal →
      (normalGen V : ℝ)≤(weight i : ℝ)/4)
    (habelian : ∀ i,Abelian F i →(Nat.card (F i) : ℝ)≤(2 : ℝ)^((weight i : ℝ)/2))
    (m r : ℕ) (hExp : ∀ i,HasExp2 (F i) (2+m)) {B : ℝ}
    (hlog : ∀ i,Real.logb 2 (Nat.card (F i))≤B) :
    (Nat.card (Family F (Multiplicative (Fin r → ZMod 4))) : ℝ)≤
      VerticalHallBase.polynomial r*
        ActualUniversalCaseINormalized.physicalCost (Fintype.card (NonabelianLabels F))
          K m (AbelianBlock F) B*
            (2 : ℝ)^markedF (∑ i : Fin t,(weight i : ℝ)) r := by
  have hsplit : (Nat.card (Family F (Multiplicative (Fin r → ZMod 4))) : ℝ)≤
      Nat.card (Family (NonabelianFactors F)
        (AbelianBlock F × Multiplicative (Fin r → ZMod 4))) := by
    exact_mod_cast Nat.card_le_card_of_injective
      (code F (Multiplicative (Fin r → ZMod 4)))
      (code_injective F (Multiplicative (Fin r → ZMod 4)))
  have ha : 0≤abelianDegree F weight := by
    apply Finset.sum_nonneg
    intro i hi
    exact Nat.cast_nonneg _
  have hrow := ActualCaseIPhysicalWord.marked_word_card_le (NonabelianFactors F)
    (nonabelianWeight F weight) K (fun j => hK (label F j).val)
    (fun j => hw (label F j).val) (fun j => hbinary (label F j).val)
    (fun j => hcard (label F j).val)
    (fun j V hV => hquarter (label F j).val (label F j).property V hV)
    m r (AbelianBlock F) (abelian_exponent F m hExp) ha
    (abelian_order_cap F weight habelian) (fun j => hlog (label F j).val)
  rw [degree_eq F weight] at hrow
  exact hsplit.trans hrow

end SymmetricSubgroupAsymptotics.MarkedC4.ActualCaseIWithAbelianFactors
