import SymmetricSubgroupAsymptotics.TernaryFourBinaryTopWreathClassBound
import SymmetricSubgroupAsymptotics.TernaryFourWreathSymmetricTopClassBound
import SymmetricSubgroupAsymptotics.TransitiveFourBinaryOrAlternating
import SymmetricSubgroupAsymptotics.WreathSubgroupClassCapacity
import SymmetricSubgroupAsymptotics.FourPointClassRepresentativeCovers
import SymmetricSubgroupAsymptotics.SmallPermutationClassBudgets

/-! Every original faithful ternary four-coordinate wreath source with
transitive top has at most360 classes. The proved top-order dichotomy
uses orbit-stabilizer and divisibility of24. Its order12/full-order cases
are identified with the actual A4/full permutation ranges before applying
their class bounds; there is no transitive-group or action census. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.TernaryFourTransitiveWreathClassBound
open TernaryWreathAffineSemidirectEquiv WreathHomProjectionRange

theorem class_card_le_threeSixty {A : Type} [Group A] [Finite A]
    (f : A →* Wreath (Fin 4)) (hf : Function.Injective f)
    (htrans : ∀ i j : Fin 4,∃g : A,(f g).right i=j) :
    Nat.card (ConjClasses A)≤360 := by
  let Q := (topProjection f).range
  have htransQ : ∀ i j : Fin 4,∃q : Q,q.val i=j := by
    intro i j
    obtain ⟨g,hg⟩ := htrans i j
    exact ⟨⟨topProjection f g,⟨g,rfl⟩⟩,hg⟩
  rcases TransitiveFourBinaryOrAlternating.card_cases Q htransQ with h4|h8|h12|h24
  · exact TernaryFourBinaryTopWreathClassBound.class_card_le_threeSixty f hf htrans
      (by change Nat.card Q≤8; omega)
  · exact TernaryFourBinaryTopWreathClassBound.class_card_le_threeSixty f hf htrans
      (by change Nat.card Q≤8; omega)
  · have hperm : Nat.card (Equiv.Perm (Fin 4))=24 := by rw [Nat.card_perm,Nat.card_fin]; rfl
    have hm := Q.card_mul_index
    rw [h12,hperm] at hm
    have hindex : Q.index=2 := by omega
    have heq : Q=alternatingGroup (Fin 4) := Equiv.Perm.eq_alternatingGroup_of_index_eq_two hindex
    have htop : Nat.card (ConjClasses (topProjection f).range)≤4 := by
      change Nat.card (ConjClasses Q)≤4
      rw [heq]
      exact FourPointClassRepresentativeCovers.alternating_class_card_le_four
    have h := WreathSubgroupClassCapacity.class_card_le_capacity_mul_top f hf 3
      (SmallPermutationClassBudgets.subgroup_class_card_le_three (Nat.card_fin 3).le)
    rw [Nat.card_fin] at h
    exact (h.trans (Nat.mul_le_mul_left _ htop)).trans (by decide)
  · have heq : Q=⊤ := Q.eq_top_of_card_eq (by rw [h24,Nat.card_perm,Nat.card_fin]; rfl)
    have ht : Function.Surjective (topProjection f) := by
      intro s
      have hs : s∈Q := by rw [heq]; trivial
      exact hs
    exact (TernaryFourWreathSymmetricTopClassBound.class_card_le_threeThirty f hf ht).trans (by decide)

end SymmetricSubgroupAsymptotics.TernaryFourTransitiveWreathClassBound
