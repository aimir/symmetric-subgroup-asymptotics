import SymmetricSubgroupAsymptotics.MarkedC4ActualCaseIWithAbelianFactors
import SymmetricSubgroupAsymptotics.MarkedC4ActualBinaryPhysicalOrderBudget
import SymmetricSubgroupAsymptotics.MarkedC4ActualBinaryAbelianBudget

/-! Actual Case-I endpoint for an ORIGINAL weighted bounded physical word
and its actual quotient maps. All physical card/exponent/log/abelian budgets
are derived here; no transitive action is assigned to a quotient. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualOriginalQuotientCaseI
open ActualFullPhysicalWordPeel ActualAbelianFactorSplit ActualBinaryPhysicalOrderBudget

theorem marked_word_card_le
    (hKP : KovacsPraegerBinaryAbelianQuotientBound)
    {t : ℕ} (degree : Fin t → ℕ) (C : ℕ)
    (hpositive : ∀ i,0<degree i) (hcut : ∀ i,degree i≤C)
    (Original : ∀ i,Subgroup (Equiv.Perm (Fin (degree i))))
    (hOriginal : ∀ i,IsPGroup 2 (Original i))
    (F : Fin t → Type) [∀ i,Group (F i)] [∀ i,Finite (F i)]
    (q : ∀ i,Original i →* F i) (onto : ∀ i,Function.Surjective (q i))
    (hcaseI : ∀ (i : Fin t),¬Abelian F i →∀ V : Subgroup (F i),V.Normal →
      (normalGen V : ℝ)≤(degree i : ℝ)/4)
    (r : ℕ) :
    (Nat.card (Family F (Multiplicative (Fin r → ZMod 4))) : ℝ)≤
      VerticalHallBase.polynomial r*
        ActualUniversalCaseINormalized.physicalCost (Fintype.card (NonabelianLabels F))
          (2^C) C (AbelianBlock F) C*
            (2 : ℝ)^markedF (∑ i : Fin t,(degree i : ℝ)) r := by
  have hbinary : ∀ i,IsPGroup 2 (F i) := fun i => (hOriginal i).of_surjective (q i) (onto i)
  have hcard : ∀ i,Nat.card (F i)≤2^degree i := fun i =>
    quotient_card_le (Original i) (hOriginal i) (q i) (onto i)
  have hmax : ∀ i,Nat.card (F i)≤2^C := fun i =>
    (hcard i).trans (pow_le_pow_right₀ (by norm_num : 1≤(2 : ℕ)) (hcut i))
  have habelian : ∀ i,Abelian F i →(Nat.card (F i) : ℝ)≤(2 : ℝ)^((degree i : ℝ)/2) := by
    intro i hi
    letI : CommGroup (F i) := { (inferInstance : Group (F i)) with mul_comm := hi }
    exact ActualBinaryAbelianBudget.section_card_le hKP (Original i) (hOriginal i) (q i) (onto i)
  have hExp : ∀ i,HasExp2 (F i) (2+C) := by
    intro i
    apply exponent_of_card_le (hbinary i) (2+C)
    exact (hmax i).trans (pow_le_pow_right₀ (by norm_num : 1≤(2 : ℕ)) (by omega : C≤2+C))
  exact ActualCaseIWithAbelianFactors.marked_word_card_le F degree (2^C) hmax
    hpositive hbinary hcard hcaseI habelian C r hExp (fun i => log_card_le C (hmax i))

end SymmetricSubgroupAsymptotics.MarkedC4.ActualOriginalQuotientCaseI
