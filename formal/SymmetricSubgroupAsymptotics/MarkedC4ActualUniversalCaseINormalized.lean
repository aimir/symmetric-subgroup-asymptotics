import SymmetricSubgroupAsymptotics.MarkedC4ActualUniversalCaseI
import SymmetricSubgroupAsymptotics.MarkedC4ActualSingleGlobalHallPolynomial

/-! Universal actual Case-I endpoint with ONE global P(r). Its remaining
cost is independent of the marking rank; no recurrence multiplies P again. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualUniversalCaseINormalized
open ActualSingleGlobalHallPolynomial

def physicalCost (t K m : ℕ) (A : Type) [CommGroup A] [Finite A] (B : ℝ) : ℝ :=
  (t.factorial*(t+1)^((2^K)*t) : ℕ)*physicalPolynomial m A*(2 : ℝ)^((t : ℝ)*B^2)

theorem actual_family_card_le {t : ℕ}
    (F : Fin t → Type) [∀ i,Group (F i)] [∀ i,Finite (F i)]
    (weight : Fin t → ℕ) (K : ℕ) (hK : ∀ i,Nat.card (F i)≤K)
    (hw : ∀ i,0<weight i) (hbinary : ∀ i,IsPGroup 2 (F i))
    (hcard : ∀ i,Nat.card (F i)≤2^weight i)
    (hquarter : ∀ (i : Fin t) (V : Subgroup (F i)),V.Normal →
      (normalGen V : ℝ)≤(weight i : ℝ)/4)
    (m r : ℕ) (A : Type) [CommGroup A] [Finite A]
    (hA : HasExp2 A (2+m)) {a B : ℝ} (ha : 0≤a)
    (hAcard : (Nat.card A : ℝ)≤(2 : ℝ)^(a/2))
    (hlog : ∀ i,Real.logb 2 (Nat.card (F i))≤B) :
    (Nat.card (ActualGlobalMenuCover.ActualFamily F
      (A × Multiplicative (Fin r → ZMod 4))) : ℝ)≤
      VerticalHallBase.polynomial r*physicalCost t K m A B*
        (2 : ℝ)^markedF (a+∑ i : Fin t,(weight i : ℝ)) r := by
  have hactual := ActualUniversalCaseI.actual_family_card_le F weight K hK hw hbinary
    hcard hquarter m r A hA ha hAcard hlog
  apply hactual.trans
  have hpoly := hall_polynomial_le_single_global m r A
  have hmenu : (0 : ℝ)≤(t.factorial*(t+1)^((2^K)*t) : ℕ) := Nat.cast_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hpoly hmenu
  apply (mul_le_mul_of_nonneg_right hmul (by positivity)).trans_eq
  rw [Real.rpow_add (by norm_num : (0 : ℝ)<2)]
  unfold physicalCost
  ring

end SymmetricSubgroupAsymptotics.MarkedC4.ActualUniversalCaseINormalized
