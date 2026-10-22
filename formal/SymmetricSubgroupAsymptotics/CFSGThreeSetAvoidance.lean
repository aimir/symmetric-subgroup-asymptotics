import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Lean.Elab.Tactic.Omega

/-! Three bounded subsets sharing a point cannot cover a finite set of
size at least three times their bound. The shared point supplies the
strict saving at the smallest field order. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGThreeSetAvoidance
variable {S : Type*} [Fintype S]

theorem exists_outside_three (A B C : Finset S) (z : S)
    (hzA:z∈A) (hzB:z∈B) (hzC:z∈C) (m:ℕ)
    (hA:A.card≤m) (hB:B.card≤m) (hC:C.card≤m) (hm:3*m≤Fintype.card S) :
    ∃x:S,x∉A ∧ x∉B ∧ x∉C := by
  classical
  have hiAB : 0<(A∩B).card := Finset.card_pos.mpr ⟨z,Finset.mem_inter.mpr ⟨hzA,hzB⟩⟩
  have hiABC : 0<((A∪B)∩C).card := Finset.card_pos.mpr
    ⟨z,Finset.mem_inter.mpr ⟨Finset.mem_union.mpr (Or.inl hzA),hzC⟩⟩
  have heAB := Finset.card_union_add_card_inter A B
  have heABC := Finset.card_union_add_card_inter (A∪B) C
  have hbound : (A∪B∪C).card+2≤3*m := by omega
  by_contra hn
  have he : A∪B∪C=Finset.univ := by
    ext x
    simp only [Finset.mem_univ,iff_true]
    by_contra hx
    apply hn
    refine ⟨x,?_,?_,?_⟩
    · intro h
      exact hx (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl h))))
    · intro h
      exact hx (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr h))))
    · intro h
      exact hx (Finset.mem_union.mpr (Or.inr h))
  rw [he,Finset.card_univ] at hbound
  omega

end SymmetricSubgroupAsymptotics.CFSGThreeSetAvoidance
