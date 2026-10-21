import SymmetricSubgroupAsymptotics.ConnectedInvolutionDerivedGeneration
import SymmetricSubgroupAsymptotics.External.CFSG.Models.YGroups

/-! Explicit ordinary generation bounds for the four actual central
quotients of Y-derived subgroups. The generator counts are 8,9,10,10.
They are not assertions of two-generation or model identification. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGGeneration
open CFSG.Models.YGroups

theorem y_adjacent_irrefl (arms : Arms) (i : Node arms) : ¬ Adjacent arms i i := by
  cases i with
  | none => exact not_false
  | some q =>
    rcases q with ⟨i, d⟩
    dsimp only [Adjacent]
    omega

theorem y_connected (arms : Arms) :
    ∀ i : Node arms, Relation.ReflTransGen (Adjacent arms) none i := by
  have hArm : ∀ (i : Fin 3) (d : ℕ) (hd : d < arms.length i),
      Relation.ReflTransGen (Adjacent arms) none (some ⟨i, ⟨d, hd⟩⟩) := by
    intro i d
    induction d with
    | zero =>
      intro hd
      exact Relation.ReflTransGen.single rfl
    | succ d ih =>
      intro hd
      have hd' : d < arms.length i := lt_trans (Nat.lt_succ_self d) hd
      apply (ih hd').tail
      exact ⟨rfl, Or.inl rfl⟩
  intro i
  cases i with
  | none => exact Relation.ReflTransGen.refl
  | some q => exact hArm q.1 q.2.val q.2.isLt

theorem y_generator_sq (arms : Arms) (i : Node arms) :
    (PresentedGroup.of (rels := relations arms) i) ^ 2 = 1 := by
  have h := PresentedGroup.one_of_mem (rels := relations arms)
    (x := (FreeGroup.of i) ^ 2) (Or.inl ⟨i, rfl⟩)
  simpa only [map_pow, PresentedGroup.of] using h

theorem y_adjacent_product_cube (arms : Arms) (i j : Node arms)
    (hij : Adjacent arms i j) :
    (PresentedGroup.of (rels := relations arms) i * PresentedGroup.of j) ^ 3 = 1 := by
  have hne : i ≠ j := by
    intro he
    subst j
    exact y_adjacent_irrefl arms i hij
  have h := PresentedGroup.one_of_mem (rels := relations arms)
    (x := (FreeGroup.of i * FreeGroup.of j) ^ 3)
    (Or.inr (Or.inl ⟨i, j, hne, hij, rfl⟩))
  simpa only [map_pow, map_mul, PresentedGroup.of] using h

theorem y_derived_generators (arms : Arms) :
    ∃ S : Finset (commutator (CFSG.Models.YGroups.Group arms)),
      Subgroup.closure (S : Set (commutator (CFSG.Models.YGroups.Group arms))) = ⊤ ∧
      S.card ≤ ∑ i : Fin 3, arms.length i := by
  have hcard : Nat.card (Node arms) - 1 = ∑ i : Fin 3, arms.length i := by
    change Nat.card (Option ((i : Fin 3) × Fin (arms.length i))) - 1 = _
    rw [Nat.card_eq_fintype_card, Fintype.card_option, Fintype.card_sigma]
    simp only [Fintype.card_fin, Nat.add_sub_cancel_right]
  have h := connected_involution_derived_generators
    (PresentedGroup.of (rels := relations arms)) none
    (PresentedGroup.closure_range_of (relations arms))
    (y_generator_sq arms) (Adjacent arms) (y_adjacent_product_cube arms) (y_connected arms)
  simpa only [hcard] using h

theorem y_simple_section_generators (arms : Arms) :
    ∃ S : Finset (SimpleSection arms),
      Subgroup.closure (S : Set (SimpleSection arms)) = ⊤ ∧
      S.card ≤ ∑ i : Fin 3, arms.length i := by
  exact generators_card_le_of_surjective (QuotientGroup.mk' _)
    (QuotientGroup.mk'_surjective _) (y_derived_generators arms)

theorem y_simple_section_aut_card_le_pow (arms : Arms) [Finite (SimpleSection arms)] :
    Nat.card (SimpleSection arms ≃* SimpleSection arms) ≤
      Nat.card (SimpleSection arms) ^ (∑ i : Fin 3, arms.length i) := by
  obtain ⟨S, hS, hcard⟩ := y_simple_section_generators arms
  exact aut_card_le_pow_of_generators S hS hcard

theorem fischer22_generators :
    ∃ S : Finset CFSG.Models.Fischer22,
      Subgroup.closure (S : Set CFSG.Models.Fischer22) = ⊤ ∧ S.card ≤ 8 := by
  have hcard : (∑ i : Fin 3, arms332.length i) = 8 := by decide
  simpa only [hcard] using y_simple_section_generators arms332

theorem fischer23_generators :
    ∃ S : Finset CFSG.Models.Fischer23,
      Subgroup.closure (S : Set CFSG.Models.Fischer23) = ⊤ ∧ S.card ≤ 9 := by
  have hcard : (∑ i : Fin 3, arms432.length i) = 9 := by decide
  simpa only [hcard] using y_simple_section_generators arms432

theorem fischer24Prime_generators :
    ∃ S : Finset CFSG.Models.Fischer24Prime,
      Subgroup.closure (S : Set CFSG.Models.Fischer24Prime) = ⊤ ∧ S.card ≤ 10 := by
  have hcard : (∑ i : Fin 3, arms442.length i) = 10 := by decide
  simpa only [hcard] using y_simple_section_generators arms442

theorem babyMonster_generators :
    ∃ S : Finset CFSG.Models.BabyMonster,
      Subgroup.closure (S : Set CFSG.Models.BabyMonster) = ⊤ ∧ S.card ≤ 10 := by
  have hcard : (∑ i : Fin 3, arms433.length i) = 10 := by decide
  simpa only [hcard] using y_simple_section_generators arms433

theorem fischer22_aut_card_le_pow_eight [Finite CFSG.Models.Fischer22] :
    Nat.card (CFSG.Models.Fischer22 ≃* CFSG.Models.Fischer22) ≤
      Nat.card CFSG.Models.Fischer22 ^ 8 := by
  obtain ⟨S, hS, hcard⟩ := fischer22_generators
  exact aut_card_le_pow_of_generators S hS hcard

theorem fischer23_aut_card_le_pow_nine [Finite CFSG.Models.Fischer23] :
    Nat.card (CFSG.Models.Fischer23 ≃* CFSG.Models.Fischer23) ≤
      Nat.card CFSG.Models.Fischer23 ^ 9 := by
  obtain ⟨S, hS, hcard⟩ := fischer23_generators
  exact aut_card_le_pow_of_generators S hS hcard

theorem fischer24Prime_aut_card_le_pow_ten [Finite CFSG.Models.Fischer24Prime] :
    Nat.card (CFSG.Models.Fischer24Prime ≃* CFSG.Models.Fischer24Prime) ≤
      Nat.card CFSG.Models.Fischer24Prime ^ 10 := by
  obtain ⟨S, hS, hcard⟩ := fischer24Prime_generators
  exact aut_card_le_pow_of_generators S hS hcard

theorem babyMonster_aut_card_le_pow_ten [Finite CFSG.Models.BabyMonster] :
    Nat.card (CFSG.Models.BabyMonster ≃* CFSG.Models.BabyMonster) ≤
      Nat.card CFSG.Models.BabyMonster ^ 10 := by
  obtain ⟨S, hS, hcard⟩ := babyMonster_generators
  exact aut_card_le_pow_of_generators S hS hcard

end SymmetricSubgroupAsymptotics.CFSGGeneration
