import SymmetricSubgroupAsymptotics.MarkedC4GeneratorNumbers
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-! Ordinary generators from the prime factors of the ACTUAL group order.
Every strict enlargement in the finite greedy construction consumes at least
one prime factor. No solvability, simple-generation, or classification input
is used; the relative statement retains literal original generators. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.FiniteGroupPrimeMultiplicityGenerators

theorem cardFactors_mono_of_dvd {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a ∣ b) : ArithmeticFunction.cardFactors a ≤ ArithmeticFunction.cardFactors b := by
  obtain ⟨k, rfl⟩ := hab
  have hk : k ≠ 0 := by intro h; simp only [h,mul_zero] at hb; exact hb rfl
  rw [ArithmeticFunction.cardFactors_mul ha hk]
  exact Nat.le_add_right _ _

theorem cardFactors_add_one_le_of_dvd_lt {a b : ℕ} (ha : 0 < a)
    (hab : a ∣ b) (hlt : a < b) :
    ArithmeticFunction.cardFactors a + 1 ≤ ArithmeticFunction.cardFactors b := by
  obtain ⟨k, hk⟩ := hab
  have hk1 : 1 < k := by
    by_contra h
    have hkle : k ≤ 1 := by omega
    have hh : b ≤ a := by rw [hk]; exact (Nat.mul_le_mul_left a hkle).trans_eq (mul_one a)
    omega
  have hp : 0 < ArithmeticFunction.cardFactors k :=
    ArithmeticFunction.cardFactors_pos_iff_one_lt.mpr hk1
  rw [hk, ArithmeticFunction.cardFactors_mul (Nat.ne_of_gt ha) (by omega : k ≠ 0)]
  omega

theorem exists_relative_generating_finset {G : Type*} [Group G] [Finite G]
    (R M : Subgroup G) (hRM : R ≤ M) :
    ∃ S : Finset G, (S : Set G) ⊆ M ∧
      Subgroup.closure ((S : Set G) ∪ R) = M ∧
      S.card + ArithmeticFunction.cardFactors (Nat.card R) ≤
        ArithmeticFunction.cardFactors (Nat.card M) := by
  suffices h : ∀ m : ℕ, ∀ S : Finset G, (S : Set G) ⊆ M →
      S.card + ArithmeticFunction.cardFactors (Nat.card R) ≤
        ArithmeticFunction.cardFactors (Nat.card (Subgroup.closure ((S : Set G) ∪ R))) →
      Nat.card M - Nat.card (Subgroup.closure ((S : Set G) ∪ R)) ≤ m →
      ∃ T : Finset G, (T : Set G) ⊆ M ∧
        Subgroup.closure ((T : Set G) ∪ R) = M ∧
        T.card + ArithmeticFunction.cardFactors (Nat.card R) ≤
          ArithmeticFunction.cardFactors (Nat.card M) by
    refine h (Nat.card M) ∅ (by simp) ?_ (Nat.sub_le _ _)
    simp only [Finset.card_empty,zero_add,Finset.coe_empty,Set.empty_union,
      Subgroup.closure_eq]
    exact le_rfl
  have hcl : ∀ S : Finset G, (S : Set G) ⊆ M →
      Subgroup.closure ((S : Set G) ∪ R) ≤ M := fun S hS =>
    (Subgroup.closure_le _).mpr (Set.union_subset hS hRM)
  intro m
  induction m with
  | zero =>
      intro S hSM hS hm
      have hle := Subgroup.card_le_of_le (hcl S hSM)
      have hcard : Nat.card (Subgroup.closure ((S : Set G) ∪ R)) = Nat.card M :=
        le_antisymm hle (by omega)
      have heq := Subgroup.eq_of_le_of_card_ge (hcl S hSM) hcard.ge
      exact ⟨S,hSM,heq,by simpa only [hcard] using hS⟩
  | succ m ih =>
      intro S hSM hS hm
      by_cases htop : Subgroup.closure ((S : Set G) ∪ R) = M
      · exact ⟨S,hSM,htop,by simpa only [htop] using hS⟩
      · obtain ⟨g,hgM,hg⟩ : ∃ g ∈ M, g ∉ Subgroup.closure ((S : Set G) ∪ R) := by
          by_contra hall
          push Not at hall
          exact htop (le_antisymm (hcl S hSM) (fun g hg => hall g hg))
        have hgS : g ∉ S := fun h => hg (Subgroup.subset_closure (Or.inl h))
        let S' := insert g S
        have hS'M : (S' : Set G) ⊆ M := by
          intro x hx
          simp only [S',Finset.coe_insert,Set.mem_insert_iff] at hx
          rcases hx with rfl | hx
          · exact hgM
          · exact hSM hx
        have hle : Subgroup.closure ((S : Set G) ∪ R) ≤
            Subgroup.closure ((S' : Set G) ∪ R) :=
          Subgroup.closure_mono (Set.union_subset_union_left _ (by simp [S']))
        have hgS' : g ∈ Subgroup.closure ((S' : Set G) ∪ R) :=
          Subgroup.subset_closure (Or.inl (by simp [S']))
        have hlt : Nat.card (Subgroup.closure ((S : Set G) ∪ R)) <
            Nat.card (Subgroup.closure ((S' : Set G) ∪ R)) := by
          refine lt_of_le_of_ne (Subgroup.card_le_of_le hle) ?_
          intro heq
          have he := Subgroup.eq_of_le_of_card_ge hle heq.ge
          exact hg (he ▸ hgS')
        have hinc := cardFactors_add_one_le_of_dvd_lt Nat.card_pos
          (Subgroup.card_dvd_of_le hle) hlt
        have hcardS' : S'.card = S.card + 1 := Finset.card_insert_of_notMem hgS
        have hM' := Subgroup.card_le_of_le (hcl S' hS'M)
        apply ih S' hS'M
        · rw [hcardS']
          omega
        · omega

theorem exists_generating_finset (G : Type*) [Group G] [Finite G] :
    ∃ S : Finset G, Subgroup.closure (S : Set G) = ⊤ ∧
      S.card ≤ ArithmeticFunction.cardFactors (Nat.card G) := by
  obtain ⟨S,_,hS,hcard⟩ := exists_relative_generating_finset (⊥ : Subgroup G) ⊤ bot_le
  refine ⟨S,?_,?_⟩
  · rw [←hS,Subgroup.closure_union,Subgroup.closure_eq,sup_bot_eq]
  · simpa only [Subgroup.card_bot,Subgroup.card_top,
      ArithmeticFunction.cardFactors_one,add_zero] using hcard

theorem genRank_le_cardFactors (G : Type*) [Group G] [Finite G] :
    MarkedC4.genRank G ≤ ArithmeticFunction.cardFactors (Nat.card G) := by
  obtain ⟨S,hS,hcard⟩ := exists_generating_finset G
  exact (MarkedC4.genRank_le hS).trans hcard

end SymmetricSubgroupAsymptotics.FiniteGroupPrimeMultiplicityGenerators
