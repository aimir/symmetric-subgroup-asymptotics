import SymmetricSubgroupAsymptotics.CFSGOrdinarySelectedTableau
import SymmetricSubgroupAsymptotics.MarkedC4ActualMenuCaseIRow

/-! Ordinary nilpotent subdirect counting from actual factor data.
The greedy order and normal-tableau menu are already constructed. The
unmarked real-log row removes the binary-only Hall/clog specialization. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGOrdinarySubdirectCount
open MarkedC4 ActualWordMenuPartition ActualSelectedDensityComparisons

variable {t : ℕ} (F : Fin t → Type) [∀ i,Group (F i)] [∀ i,Finite (F i)]
    (weight : Fin t → ℕ)

/-- An occupied menu is bounded using its actual representative. -/
theorem occupied_family_card_le (H : Family F) (C d B : ℝ)
    (hC : 0 < C) (hd : 0 ≤ d) (hw : ∀ i,0 < weight i)
    (horder : ∀ i,Real.logb 2 (Nat.card (F i)) ≤ C*weight i)
    (hbounded : ∀ i,Real.logb 2 (Nat.card (F i)) ≤ B)
    (hnormal : ∀ i (N : Subgroup (F i)) [N.Normal],(normalGen N : ℝ) ≤ d*weight i) :
    (Nat.card (MenuFamily F (key F weight H)) : ℝ) ≤ 
      (2 : ℝ)^(C*d*(∑ i : Fin t,(weight i : ℝ))^2/4+(t : ℝ)*B^2) := by
  let c : Fin t → ℝ := fun i => ActualMenuCaseIRow.density F weight H i/C
  let n : Fin t → ℝ := fun i => weight ((key F weight H).1 i)
  have hcancel (i : Fin t) : C*c i=ActualMenuCaseIRow.density F weight H i := by
    dsimp [c]
    field_simp [ne_of_gt hC]
  have hc0 (i : Fin t) : 0 ≤ c i :=
    div_nonneg (ActualBinaryLogDensityBinding.selectedDensity_nonneg F H.val weight
      (selectedPlan F weight H) (ActualMenuCaseIRow.index F weight H i)) hC.le
  have hc1 (i : Fin t) : c i ≤ 1 := by
    apply (div_le_one hC).mpr
    exact CFSGOrdinarySelectedTableau.selectedDensity_le F H.val weight
      (selectedPlan F weight H) C hw horder (ActualMenuCaseIRow.index F weight H i)
  have hmono : Monotone c := by
    intro i j hij
    exact div_le_div_of_nonneg_right (selectedDensity_mono F H.val weight
      (selectedPlan F weight H) hij) hC.le
  have hcount := CFSGOrdinaryTableauCount.card_le_quadratic
    (menuFactors F (key F weight H)) (menuDiagonal F (key F weight H))
    (menuTableau F (key F weight H)) (toMenu F weight H) c n C d B hC.le hd hc0 hc1
    (fun _ => Nat.cast_nonneg _) hmono
    (by intro i j hji;rw [hcancel];exact ActualMenuCaseIRow.entry_log_bound F weight H hw i j hji)
    (by intro i;rw [hcancel];exact ActualMenuCaseIRow.diagonal_log F weight H hw i)
    (by
      intro i
      letI : (menuDiagonal F (key F weight H) i).Normal := by
        rw [←(toMenu F weight H).val.property.2.2 i]
        exact ActualSubdirectFiltration.diagonalNormal _ _ (toMenu F weight H).val.property.1 i
      exact hnormal ((key F weight H).1 i) (menuDiagonal F (key F weight H) i))
    (fun i => hbounded ((key F weight H).1 i))
  have hn : (∑ i : Fin t,n i)=∑ i : Fin t,(weight i : ℝ) :=
    by
      apply Fintype.sum_equiv (key F weight H).1
      intro i
      rfl
  rw [hn] at hcount
  exact hcount

/-- A genuine ordinary subdirect-product bound, including all actual
nilpotent sources and every selected physical order, with one finite menu
factor. No enumeration/counting hypothesis occurs. -/
theorem subdirect_card_le (C d B : ℝ) (K : ℕ)
    (hC : 0 < C) (hd : 0 ≤ d) (hw : ∀ i,0 < weight i)
    (horder : ∀ i,Real.logb 2 (Nat.card (F i)) ≤ C*weight i)
    (hbounded : ∀ i,Real.logb 2 (Nat.card (F i)) ≤ B)
    (hK : ∀ i,Nat.card (F i) ≤ K)
    (hnormal : ∀ i (N : Subgroup (F i)) [N.Normal],(normalGen N : ℝ) ≤ d*weight i) :
    (Nat.card (Family F) : ℝ) ≤ 
      (t.factorial*(t+1)^((2^K)*t) : ℕ)*
        (2 : ℝ)^(C*d*(∑ i : Fin t,(weight i : ℝ))^2/4+(t : ℝ)*B^2) := by
  let O := ActualOccupiedMenuCover.Occupied F weight
  letI : Fintype O := Fintype.ofFinite _
  let V (q : O) := {H : Family F // key F weight H=q.val}
  let code : Family F → Σ q : O,V q :=
    fun H => ⟨⟨key F weight H,⟨H,rfl⟩⟩,⟨H,rfl⟩⟩
  have hinj : Function.Injective code := by
    intro H J h
    exact congrArg (fun z : Σ q : O,V q => z.2.val) h
  have hsum : Nat.card (Family F) ≤ ∑ q : O,Nat.card (V q) :=
    (Nat.card_le_card_of_injective code hinj).trans_eq (by rw [Nat.card_sigma])
  have hlocal (q : O) : (Nat.card (V q) : ℝ) ≤ 
      (2 : ℝ)^(C*d*(∑ i : Fin t,(weight i : ℝ))^2/4+(t : ℝ)*B^2) := by
    have hle := Nat.card_le_card_of_injective (fibreMap F weight q.val)
      (fibreMap_injective F weight q.val)
    have hleR : (Nat.card (V q) : ℝ) ≤ Nat.card (MenuFamily F q.val) := by exact_mod_cast hle
    apply hleR.trans
    have hh := occupied_family_card_le F weight
      (ActualOccupiedMenuCover.representative F weight q) C d B hC hd hw horder hbounded hnormal
    simpa only [ActualOccupiedMenuCover.representative_key] using hh
  have hO := ActualOccupiedMenuCover.occupied_menu_card_le F weight K hK
  have hOR : (Nat.card O : ℝ) ≤ (t.factorial*(t+1)^((2^K)*t) : ℕ) := by exact_mod_cast hO
  calc
    _  ≤  ∑ q : O,(Nat.card (V q) : ℝ) := by exact_mod_cast hsum
    _  ≤  ∑ _q : O,(2 : ℝ)^(C*d*(∑ i : Fin t,(weight i : ℝ))^2/4+(t : ℝ)*B^2) :=
      Finset.sum_le_sum (fun q _ => hlocal q)
    _ = (Nat.card O : ℝ)*(2 : ℝ)^(C*d*(∑ i : Fin t,(weight i : ℝ))^2/4+(t : ℝ)*B^2) := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card]
    _  ≤  _ := mul_le_mul_of_nonneg_right hOR (by positivity)

end SymmetricSubgroupAsymptotics.CFSGOrdinarySubdirectCount
