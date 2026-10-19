import SymmetricSubgroupAsymptotics.AlternatingTopImageNormalGenerators
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.PGroup

/-! Every actual transitive four-point block image is binary or contains
A4. The proof uses orbit-stabilizer and the divisors of24, not a subgroup
or catalogue enumeration. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TransitiveFourBinaryOrAlternating

theorem card_cases (B : Subgroup (Equiv.Perm (Fin 4)))
    (htrans : ∀ x y : Fin 4, ∃ g : B, (g : Equiv.Perm (Fin 4)) x=y) :
    Nat.card B=4 ∨ Nat.card B=8 ∨ Nat.card B=12 ∨ Nat.card B=24 := by
  letI : MulAction.IsPretransitive B (Fin 4) := ⟨htrans⟩
  have hd4 : 4∣Nat.card B := by
    have h := (MulAction.stabilizer B (0 : Fin 4)).index_dvd_card
    simpa only [MulAction.index_stabilizer_of_transitive,Nat.card_fin] using h
  have hd24 : Nat.card B∣24 := by
    have h := B.card_subgroup_dvd_card
    simpa only [Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin] using h
  have hp : 0<Nat.card B := Nat.card_pos
  obtain ⟨c,hc⟩ := hd24
  have hcp : 0<c := by
    by_contra hn
    have : c=0 := by omega
    subst c
    simp at hc
  have hcl : c≤24 := by nlinarith
  interval_cases c <;> omega

theorem binary_or_alternating (B : Subgroup (Equiv.Perm (Fin 4)))
    (htrans : ∀ x y : Fin 4, ∃ g : B, (g : Equiv.Perm (Fin 4)) x=y) :
    IsPGroup 2 B ∨ alternatingGroup (Fin 4)≤B := by
  rcases card_cases B htrans with h4 | h8 | h12 | h24
  · exact Or.inl (IsPGroup.of_card (n := 2) (by simpa using h4))
  · exact Or.inl (IsPGroup.of_card (n := 3) (by simpa using h8))
  · right
    have hm := B.card_mul_index
    have hc : Nat.card (Equiv.Perm (Fin 4))=24 := by
      rw [Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin]
      norm_num
    rw [h12,hc] at hm
    have hi : B.index=2 := by omega
    rw [Equiv.Perm.eq_alternatingGroup_of_index_eq_two hi]
  · right
    have ht : B=⊤ := B.eq_top_of_card_eq (by
      simpa only [Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin] using h24)
    rw [ht]
    exact le_top

end SymmetricSubgroupAsymptotics.TransitiveFourBinaryOrAlternating
