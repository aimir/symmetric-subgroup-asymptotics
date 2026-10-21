import SymmetricSubgroupAsymptotics.CFSGOrdinarySubdirectCount
import SymmetricSubgroupAsymptotics.CFSGOrdinaryTableauEnergyCount
import SymmetricSubgroupAsymptotics.CFSGOrdinaryExceptionalDensityEnergy
import SymmetricSubgroupAsymptotics.CFSGOddNilpotentSharpNormalRank
import SymmetricSubgroupAsymptotics.CFSGOddNilpotentOrderDensity
import SymmetricSubgroupAsymptotics.CFSGOrdinaryTernarySubdirectCount

/-! Count ALL actual odd-nilpotent subdirect sources using their SAME
faithful transitive factor actions. The mixed-prime normal-rank and order
profiles are proved internally; the degree-three exceptional cut is the
same exact one as in the checked ternary table argument. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGOddNilpotentSubdirectCount
open MarkedC4 ActualWordMenuPartition ActualSelectedDensityComparisons
open CFSGPrimeOrdinaryFactorProfile

/-- The fixed-density exceptional coefficient has a strict quadratic gap. -/
theorem ternary_coefficient_lt : Real.logb 2 3/27 < (1/16 : ℝ) := by
  have hp : (3 : ℝ)^16 < (2 : ℝ)^27 := by norm_num
  have hl := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2)
    (by positivity : (0 : ℝ) < (3 : ℝ)^16) hp
  rw [Real.logb_pow,Real.logb_pow,Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),mul_one] at hl
  norm_num only [Nat.cast_ofNat] at hl
  linarith

variable {t : ℕ} (X : Fin t → Type) [∀ i,Finite (X i)] [∀ i,Nonempty (X i)]
    (U : ∀ i,Subgroup (Equiv.Perm (X i)))
    [∀ i,MulAction.IsPretransitive (U i) (X i)]
    [∀ i,Group.IsNilpotent (U i)] (hodd : ∀ i,¬2 ∣ Nat.card (U i))

include hodd

/-- The occupied menu is the one selected by the actual source. -/
theorem occupied_family_card_le (H : Family (fun i => U i)) (B : ℝ)
    (hbounded : ∀ i,Real.logb 2 (Nat.card (U i)) ≤ B) :
    (Nat.card (MenuFamily (fun i => U i) (key (fun i => U i) (fun i => Nat.card (X i)) H)) : ℝ) ≤
      (2 : ℝ)^((Real.logb 2 3/27)*(∑ i : Fin t,(Nat.card (X i) : ℝ))^2+(t : ℝ)*B^2) := by
  let F : Fin t → Type := fun i => U i
  let weight : Fin t → ℕ := fun i => Nat.card (X i)
  let C : ℝ := Real.logb 2 3/2
  let c : Fin t → ℝ := fun i => ActualMenuCaseIRow.density F weight H i/C
  let n : Fin t → ℝ := fun i => weight ((key F weight H).1 i)
  let D := menuDiagonal F (key F weight H)
  let P : Fin t → Prop := fun i => Nat.card (X ((key F weight H).1 i))=3 ∧ D i≠⊥
  have hlog3 : 0 < Real.logb 2 3 := Real.logb_pos (by norm_num) (by norm_num)
  have hC : 0 < C := div_pos hlog3 (by norm_num)
  have hw : ∀ i,0 < weight i := fun i => Nat.card_pos
  have horder (i : Fin t) : Real.logb 2 (Nat.card (F i)) ≤ C*weight i := by
    have hh := CFSGOddNilpotentOrderDensity.log_order_le (X := X i) (hodd i)
    simpa only [F,C,weight] using hh
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
  letI (i : Fin t) : (D i).Normal := by
    rw [show D i=menuDiagonal F (key F weight H) i from rfl,
      ←(toMenu F weight H).val.property.2.2 i]
    exact ActualSubdirectFiltration.diagonalNormal _ _ (toMenu F weight H).val.property.1 i
  have hP (i : Fin t) (hi : P i) : c i=2/3 := by
    have hd3 : Nat.card (D i)=3 :=
      CFSGOddPermutationDensity.nontrivial_subgroup_degree_three_card
        (X := X ((key F weight H).1 i)) (hodd _) hi.1 (D i) hi.2
    have hd := ActualMenuCaseIRow.diagonal_log F weight H hw i
    change Real.logb 2 (Nat.card (D i))=ActualMenuCaseIRow.density F weight H i*n i at hd
    have hn3 : n i=3 := by
      dsimp [n,weight]
      exact_mod_cast hi.1
    rw [hd3,hn3,←hcancel] at hd
    dsimp [C] at *
    nlinarith
  have hrank (i : Fin t) : (normalGen (D i) : ℝ) ≤ (2/9)*n i+
      (if P i then (1/9)*n i else 0) := by
    have ht := CFSGOddNilpotentSharpNormalRank.normalGen_real_le_with_exception
      (X := X ((key F weight H).1 i)) (hodd _) (D i)
    exact ht
  have he := CFSGOrdinaryTableauEnergy.ternary_ranked_energy_le P c n
    (fun i => (normalGen (D i) : ℝ)) hc0 hc1 (fun _ => Nat.cast_nonneg _) hmono hP (by
      intro i
      have hiR := hrank i
      by_cases hi : P i
      · rw [if_pos hi] at hiR ⊢
        exact hiR
      · rw [if_neg hi] at hiR ⊢
        exact hiR)
  have hc := CFSGOrdinaryTableauCount.card_le_of_energy
    (menuFactors F (key F weight H)) D (menuTableau F (key F weight H))
    (toMenu F weight H) c n C B ((2/27)*(∑ i : Fin t,n i)^2) hC.le
    (by intro i j hji;rw [hcancel];exact ActualMenuCaseIRow.entry_log_bound F weight H hw i j hji)
    (by intro i;rw [hcancel];exact ActualMenuCaseIRow.diagonal_log F weight H hw i)
    (fun i => hbounded ((key F weight H).1 i)) he
  have hn : (∑ i : Fin t,n i)=∑ i : Fin t,(Nat.card (X i) : ℝ) :=
    by
      apply Fintype.sum_equiv (key F weight H).1
      intro i
      rfl
  rw [hn] at hc
  convert hc using 1 <;> dsimp [C] <;> ring

/-- Full actual ternary subdirect counting, including all occupied menus.
No externally supplied rank, selected-tableau or counting premise occurs. -/
theorem subdirect_card_le (B : ℝ) (K : ℕ)
    (hbounded : ∀ i,Real.logb 2 (Nat.card (U i)) ≤ B)
    (hK : ∀ i,Nat.card (U i) ≤ K) :
    (Nat.card (Family (fun i => U i)) : ℝ) ≤
      (t.factorial*(t+1)^((2^K)*t) : ℕ)*
        (2 : ℝ)^((Real.logb 2 3/27)*(∑ i : Fin t,(Nat.card (X i) : ℝ))^2+(t : ℝ)*B^2) := by
  let F : Fin t → Type := fun i => U i
  let weight : Fin t → ℕ := fun i => Nat.card (X i)
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
      (2 : ℝ)^((Real.logb 2 3/27)*(∑ i : Fin t,(Nat.card (X i) : ℝ))^2+(t : ℝ)*B^2) := by
    have hle := Nat.card_le_card_of_injective (fibreMap F weight q.val)
      (fibreMap_injective F weight q.val)
    have hleR : (Nat.card (V q) : ℝ) ≤ Nat.card (MenuFamily F q.val) := by exact_mod_cast hle
    apply hleR.trans
    have hh := occupied_family_card_le X U hodd (ActualOccupiedMenuCover.representative F weight q) B hbounded
    change (Nat.card (MenuFamily F (key F weight
      (ActualOccupiedMenuCover.representative F weight q))) : ℝ) ≤ _ at hh
    rw [ActualOccupiedMenuCover.representative_key] at hh
    exact hh
  have hO := ActualOccupiedMenuCover.occupied_menu_card_le F weight K hK
  have hOR : (Nat.card O : ℝ) ≤ (t.factorial*(t+1)^((2^K)*t) : ℕ) := by exact_mod_cast hO
  calc
    _ ≤ ∑ q : O,(Nat.card (V q) : ℝ) := by exact_mod_cast hsum
    _ ≤ ∑ _q : O,(2 : ℝ)^((Real.logb 2 3/27)*(∑ i : Fin t,(Nat.card (X i) : ℝ))^2+(t : ℝ)*B^2) :=
      Finset.sum_le_sum (fun q _ => hlocal q)
    _ = (Nat.card O : ℝ)*(2 : ℝ)^((Real.logb 2 3/27)*(∑ i : Fin t,(Nat.card (X i) : ℝ))^2+(t : ℝ)*B^2) := by
      simp [Nat.card_eq_fintype_card]
    _ ≤ _ := mul_le_mul_of_nonneg_right hOR (by positivity)

end SymmetricSubgroupAsymptotics.CFSGOddNilpotentSubdirectCount
