import SymmetricSubgroupAsymptotics.MarkedC4ActualMenuCaseIRow

/-! Universal Case-I count of the ACTUAL physical/Hall family. The only
alphabet cost is the fixed original-order/tableau menu, paid once. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualUniversalCaseI
open ActualWordMenuPartition ActualMenuCaseIRow ActualOccupiedMenuCover

variable {t : ℕ} (F : Fin t → Type) [∀ i,Group (F i)] [∀ i,Finite (F i)]
  (weight : Fin t → ℕ)

theorem total_degree_eq (q : Menu F) :
    prefixWeight (nAt F weight q) t=∑ i : Fin t,(weight i : ℝ) := by
  have hs : (∑ i : Fin t,(weight (q.1 i) : ℝ))=
      ∑ m ∈ Finset.range t,nAt F weight q m := by
    apply Finset.sum_bij (fun i _ => i.val)
    · intro i hi
      exact Finset.mem_range.mpr i.isLt
    · intro i hi j hj he
      exact Fin.ext he
    · intro m hm
      exact ⟨⟨m,Finset.mem_range.mp hm⟩,Finset.mem_univ _,rfl⟩
    · intro i hi
      simp only [nAt,dif_pos i.isLt]
  exact hs.symm.trans (Fintype.sum_equiv q.1
    (fun i => (weight (q.1 i) : ℝ)) (fun i => (weight i : ℝ)) (fun _ => rfl))

local instance : Fintype (Occupied F weight) := Fintype.ofFinite _
local instance (q : Occupied F weight) : Fintype (MenuFamily F q.val) := Fintype.ofFinite _

/-- All actual sources are summed, each with its actual Hall fibre into
A times ONE C4^r. No count, capacity or encoding premise appears here. -/
theorem actual_family_card_le
    (K : ℕ) (hK : ∀ i,Nat.card (F i)≤K)
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
      (t.factorial*(t+1)^((2^K)*t) : ℕ)*
        ((∏ k ∈ Finset.range (2+m),
          ((col (A × Multiplicative (Fin r → ZMod 4)) k : ℝ)+1))*4^(2+m))*
          (2 : ℝ)^(markedF (a+∑ i : Fin t,(weight i : ℝ)) r+(t : ℝ)*B^2) := by
  let E := A × Multiplicative (Fin r → ZMod 4)
  let C : ℝ := ((∏ k ∈ Finset.range (2+m),((col E k : ℝ)+1))*4^(2+m))*
    (2 : ℝ)^(markedF (a+∑ i : Fin t,(weight i : ℝ)) r+(t : ℝ)*B^2)
  have hC : 0≤C := by dsimp [C]; positivity
  have hrow (q : Occupied F weight) :
      (Nat.card (Σ U : MenuFamily F q.val,
        AbelianProductGraphClassification.FullSecond E U.val.val) : ℝ)≤C := by
    obtain ⟨H,hH⟩ := q.property
    letI : Fintype (MenuFamily F (key F weight H)) := Fintype.ofFinite _
    have hh := menu_hall_sum_le F weight H hw hbinary hcard hquarter
      m r A hA ha hAcard hlog
    rw [total_degree_eq F weight] at hh
    have hc : (Nat.card (Σ U : MenuFamily F (key F weight H),
        AbelianProductGraphClassification.FullSecond E U.val.val) : ℝ)≤C := by
      rw [Nat.card_sigma,Nat.cast_sum]
      exact hh
    have he := congrArg (fun p : Menu F =>
      (Nat.card (Σ U : MenuFamily F p,
        AbelianProductGraphClassification.FullSecond E U.val.val) : ℝ)) hH
    exact (le_of_eq he.symm).trans hc
  have hcover : (Nat.card (ActualGlobalMenuCover.ActualFamily F E) : ℝ)≤
      (Nat.card (Cover F weight E) : ℝ) := by
    exact_mod_cast card_le_cover F weight E
  have hmenu : (Nat.card (Occupied F weight) : ℝ)≤
      (t.factorial*(t+1)^((2^K)*t) : ℕ) := by
    exact_mod_cast occupied_menu_card_le F weight K hK
  calc
    _≤(Nat.card (Cover F weight E) : ℝ) := hcover
    _=∑ q : Occupied F weight,(Nat.card (Σ U : MenuFamily F q.val,
        AbelianProductGraphClassification.FullSecond E U.val.val) : ℝ) := by
      rw [Nat.card_sigma,Nat.cast_sum]
    _≤∑ _q : Occupied F weight,C := Finset.sum_le_sum (fun q _ => hrow q)
    _=(Nat.card (Occupied F weight) : ℝ)*C := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card]
    _≤(t.factorial*(t+1)^((2^K)*t) : ℕ)*C := mul_le_mul_of_nonneg_right hmenu hC
    _=_ := by dsimp [C,E]; ring

end SymmetricSubgroupAsymptotics.MarkedC4.ActualUniversalCaseI
