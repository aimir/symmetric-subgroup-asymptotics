import SymmetricSubgroupAsymptotics.BinaryBooleanFourLargeQuadraticSet

/-! A cubic leading support, together with any incomparable support of
size at least two, supplies four quadratic leading supports by actual
leading derivatives. Only individual support incidences are checked. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryBooleanFourPolynomialCoordinates
open BinaryElementaryPairMonomialWidth

def quadraticDownset (a : Fin 16) : Finset (Fin 16) :=
  quadraticMasks.filter (fun b => support b ⊆ support a)

private theorem cubic_downset_card : ∀ a : Fin 16,
    (support a).card = 3 → (quadraticDownset a).card = 3 := by decide

private theorem quadratic_outside_cubic : ∀ a b : Fin 16,
    (support a).card = 3 → 2 ≤ (support b).card → ¬support b ⊆ support a →
      ∃ q ∈ quadraticMasks, support q ⊆ support b ∧ ¬support q ⊆ support a := by decide

def quadraticShadow (L : Finset (Fin 16)) : Finset (Fin 16) :=
  quadraticMasks.filter (fun q => ∃ a ∈ L, support q ⊆ support a)

theorem quadraticShadow_card_ge_four_of_cubic
    (L : Finset (Fin 16))
    (hA : IsAntichain (fun a b => support a ⊆ support b) (L : Set (Fin 16)))
    (hcard : 2 ≤ L.card) (hlow : ∀ b ∈ L, 2 ≤ (support b).card)
    (a : Fin 16) (ha : a ∈ L) (hac : (support a).card = 3) :
    4 ≤ (quadraticShadow L).card := by
  classical
  obtain ⟨b, hb, hba⟩ := Finset.exists_mem_ne (by omega : 1 < L.card) a
  have hnot : ¬support b ⊆ support a := fun h => hA hb ha hba h
  obtain ⟨q, hq, hqb, hqa⟩ := quadratic_outside_cubic a b hac (hlow b hb) hnot
  have hqnot : q ∉ quadraticDownset a := by
    intro h
    exact hqa (Finset.mem_filter.mp h).2
  have hsub : insert q (quadraticDownset a) ⊆ quadraticShadow L := by
    intro c hc
    apply Finset.mem_filter.mpr
    rcases Finset.mem_insert.mp hc with he | he
    · subst c
      exact ⟨hq, b, hb, hqb⟩
    · obtain ⟨hcQ, hca⟩ := Finset.mem_filter.mp he
      exact ⟨hcQ, a, ha, hca⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hqnot, cubic_downset_card a hac] at hc
  exact hc

end SymmetricSubgroupAsymptotics.BinaryBooleanFourPolynomialCoordinates
