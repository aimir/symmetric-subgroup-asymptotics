import SymmetricSubgroupAsymptotics.BinaryFourQuadraticAdjacentWidth
import SymmetricSubgroupAsymptotics.BinaryBooleanFourSupportRelabel
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Pi

/-! The selected adjacent-pair certificate applies to any two missing
quadratic supports related by an abstract variable permutation. The
permutation acts solely on the finite antichain labels. -/
set_option autoImplicit false
set_option maxRecDepth 10000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryFourQuadraticAdjacentConsumer
open BinaryElementaryPairMonomialWidth

def Allowed (m n : Fin 16) (s : Finset (Fin 4)) : Prop :=
  s.card ≤ 1 ∨ (s.card = 2 ∧ s ≠ support m ∧ s ≠ support n)

def Raises (m n : Fin 16) (a b : Monomial) : Prop :=
  if a.1 then (if b.1 then support b.2 ⊆ support a.2 else Allowed m n (support b.2 \ support a.2))
  else b.1 = false ∧ support b.2 ⊆ support a.2

set_option maxHeartbeats 2000000 in
private theorem adjacent_support_relabel : ∀ m n : Fin 16,
    (support m).card = 2 → (support n).card = 2 → (support m ∩ support n).card = 1 →
    ∃ p : Equiv.Perm (Fin 4),
      (support m).map p.toEmbedding = support 3 ∧
      (support n).map p.toEmbedding = support 5 := by
  have h : ∀ m n : Fin 16,
      (support m).card = 2 → (support n).card = 2 → (support m ∩ support n).card = 1 →
      ∃ f : Fin 4 → Fin 4, (∀ i j, f i = f j → i = j) ∧
        (support m).image f = support 3 ∧ (support n).image f = support 5 := by decide
  intro m n hm hn hmn
  obtain ⟨f, hf, hfm, hfn⟩ := h m n hm hn hmn
  let p := Equiv.ofBijective f
    (Function.Injective.bijective_of_finite (show Function.Injective f from hf))
  refine ⟨p, ?_, ?_⟩
  · simpa only [Finset.map_eq_image] using hfm
  · simpa only [Finset.map_eq_image] using hfn

theorem raises_relabel_iff (p : Equiv.Perm (Fin 4)) (m n : Fin 16)
    (hm : (support m).map p.toEmbedding = support 3)
    (hn : (support n).map p.toEmbedding = support 5) (a b : Monomial) :
    BinaryFourQuadraticAdjacentWidth.Raises (BinaryBooleanFourSupportRelabel.monomial p a) (BinaryBooleanFourSupportRelabel.monomial p b) ↔
      Raises m n a b := by
  rcases a with ⟨l, a⟩
  rcases b with ⟨r, b⟩
  cases l <;> cases r <;>
    simp only [BinaryBooleanFourSupportRelabel.monomial_apply, BinaryFourQuadraticAdjacentWidth.Raises, Raises,
      Bool.false_eq_true, Bool.true_eq_false, if_false, if_true,
      BinaryBooleanFourSupportRelabel.support_mask, Finset.map_subset_map, false_and, true_and]
  change BinaryFourQuadraticAdjacentWidth.Allowed
    ((support b).map p.toEmbedding \ (support a).map p.toEmbedding) ↔
      Allowed m n (support b \ support a)
  rw [← Finset.map_sdiff]
  let s := support b \ support a
  have hem : s.map p.toEmbedding ≠ support 3 ↔ s ≠ support m := by
    rw [← hm]
    exact not_congr (Finset.map_inj (f := p.toEmbedding))
  have hen : s.map p.toEmbedding ≠ support 5 ↔ s ≠ support n := by
    rw [← hn]
    exact not_congr (Finset.map_inj (f := p.toEmbedding))
  change BinaryFourQuadraticAdjacentWidth.Allowed (s.map p.toEmbedding) ↔ Allowed m n s
  unfold BinaryFourQuadraticAdjacentWidth.Allowed Allowed
  rw [Finset.card_map]
  exact or_congr Iff.rfl (and_congr Iff.rfl (and_congr hem hen))

theorem antichain_card_le_seven (p : Equiv.Perm (Fin 4)) (m n : Fin 16)
    (hm : (support m).map p.toEmbedding = support 3)
    (hn : (support n).map p.toEmbedding = support 5)
    (s : Finset Monomial) (hs : IsAntichain (Raises m n) (s : Set Monomial)) : s.card ≤ 7 := by
  classical
  let e := BinaryBooleanFourSupportRelabel.monomial p
  have ht : IsAntichain BinaryFourQuadraticAdjacentWidth.Raises
      (s.map e.toEmbedding : Set Monomial) := by
    intro a ha b hb hne hab
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hb
    exact hs hx hy (fun he => hne (congrArg e he))
      ((raises_relabel_iff p m n hm hn x y).mp hab)
  have hb := BinaryFourQuadraticAdjacentWidth.antichain_card_le_seven _ ht
  simpa only [Finset.card_map] using hb

theorem antichain_card_le_seven_of_adjacent (m n : Fin 16)
    (hm : (support m).card = 2) (hn : (support n).card = 2)
    (hmn : (support m ∩ support n).card = 1)
    (s : Finset Monomial) (hs : IsAntichain (Raises m n) (s : Set Monomial)) : s.card ≤ 7 := by
  obtain ⟨p, hp, hq⟩ := adjacent_support_relabel m n hm hn hmn
  exact antichain_card_le_seven p m n hp hq s hs

end SymmetricSubgroupAsymptotics.BinaryFourQuadraticAdjacentConsumer
