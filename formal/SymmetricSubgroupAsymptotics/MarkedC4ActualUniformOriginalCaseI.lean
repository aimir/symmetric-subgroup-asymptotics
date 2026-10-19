import SymmetricSubgroupAsymptotics.MarkedC4ActualOriginalQuotientCaseI
import SymmetricSubgroupAsymptotics.MarkedC4ActualUniformCaseICost

/-! Uniform Case-I estimate for actual quotients of an original bounded
binary permutation word. The physical cost is independent of marking rank. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualUniformOriginalCaseI
open ActualFullPhysicalWordPeel ActualAbelianFactorSplit ActualBinaryPhysicalOrderBudget

def costExponent (C b : ℕ) : ℝ :=
  (((1+2^(2^C))*b+3*C+2 : ℕ) : ℝ)+(b : ℝ)*(C : ℝ)^2

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
        (((∑ i : Fin t,degree i : ℕ) : ℝ)+2)^
          costExponent C (∑ i : Fin t,degree i)*
            (2 : ℝ)^markedF (∑ i : Fin t,(degree i : ℝ)) r := by
  let b : ℕ := ∑ i : Fin t,degree i
  have ht : t≤b := by
    calc
      t=∑ _i : Fin t,1 := by simp
      _≤∑ i : Fin t,degree i := Finset.sum_le_sum (fun i _ => hpositive i)
  have hn : Fintype.card (NonabelianLabels F)≤b := by
    have hh : Fintype.card (NonabelianLabels F)≤t := by
      simpa only [Nat.card_eq_fintype_card,Fintype.card_fin] using
        (Nat.card_le_card_of_injective
          (fun i : NonabelianLabels F => i.val) Subtype.val_injective)
    exact hh.trans ht
  have habelian : ∀ i,Abelian F i →(Nat.card (F i) : ℝ)≤(2 : ℝ)^((degree i : ℝ)/2) := by
    intro i hi
    letI : CommGroup (F i) := { (inferInstance : Group (F i)) with mul_comm := hi }
    exact ActualBinaryAbelianBudget.section_card_le hKP (Original i) (hOriginal i) (q i) (onto i)
  have hab : abelianDegree F degree≤(b : ℝ) := by
    have hd := degree_eq F degree
    have hnon : 0≤∑ j : Fin (Fintype.card (NonabelianLabels F)),
        (nonabelianWeight F degree j : ℝ) :=
      Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
    have hb : (b : ℝ)=∑ i : Fin t,(degree i : ℝ) := by simp [b]
    linarith
  have hAcap : (Nat.card (AbelianBlock F) : ℝ)≤(2 : ℝ)^((b : ℝ)/2) :=
    (abelian_order_cap F degree habelian).trans
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith))
  have hExp : ∀ i,HasExp2 (F i) (2+C) := by
    intro i
    have hi := hcut i
    apply exponent_of_card_le ((hOriginal i).of_surjective (q i) (onto i)) (2+C)
    exact (quotient_card_le (Original i) (hOriginal i) (q i) (onto i)).trans
      (pow_le_pow_right₀ (by norm_num : 1≤(2 : ℕ)) (by omega : degree i≤2+C))
  have hcost := ActualUniformCaseICost.physical_cost_le
    (Fintype.card (NonabelianLabels F)) (2^C) C b hn (AbelianBlock F)
    (abelian_exponent F C hExp) hAcap (C : ℝ)
  have hrow := ActualOriginalQuotientCaseI.marked_word_card_le hKP degree C
    hpositive hcut Original hOriginal F q onto hcaseI r
  apply hrow.trans
  have hP : (0 : ℝ)≤VerticalHallBase.polynomial r := by
    unfold VerticalHallBase.polynomial
    positivity
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hcost hP) (by positivity)

end SymmetricSubgroupAsymptotics.MarkedC4.ActualUniformOriginalCaseI
