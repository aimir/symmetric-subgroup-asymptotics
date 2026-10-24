import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleWordInjective

/-! The genuine middle fixed-root parameter map is injective, and its
range inside the pinned original fixed subgroup has exactly q squared
points. No derived or central-quotient passage is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleFixedParameters
open CFSGReeFFourMiddleFixedWords CFSGReeFFourMiddleWordInjective
open CFSGReeFFourFieldParameters CFSGReeFFourFixedModelEquivalence

theorem fixedMiddleWord_injective (m : ℕ) :
    Function.Injective (fun p : Field m×Field m=>fixedMiddleWord m p.1 p.2) := by
  rintro ⟨a,c⟩ ⟨a',c'⟩ he
  have h := middleWord_parameters_eq m a (alpha m a) c (alpha m c+a^2*alpha m a)
    a' (alpha m a') c' (alpha m c'+a'^2*alpha m a') he
  exact Prod.ext h.1 h.2.2.1

theorem fixedMiddleParameter_injective (m : ℕ) :
    Function.Injective (fixedMiddleParameter m) := by
  intro p q he
  apply fixedMiddleWord_injective m
  exact congrArg (fun g : originalModelFixed m=>g.val) he

theorem originalFixedMiddleParameter_injective (m : ℕ) :
    Function.Injective (originalFixedMiddleParameter m) := by
  intro p q he
  apply fixedMiddleParameter_injective m
  exact (originalFixedEquiv m).symm.injective he

theorem fixedMiddleParameter_range_card (m : ℕ) :
    Nat.card (Set.range (fixedMiddleParameter m))=(2^(2*m+1))^2 := by
  rw [Nat.card_range_of_injective (fixedMiddleParameter_injective m)]
  simp only [Nat.card_prod,field_card,pow_two]

theorem originalFixedMiddleParameter_range_card (m : ℕ) :
    Nat.card (Set.range (originalFixedMiddleParameter m))=(2^(2*m+1))^2 := by
  rw [Nat.card_range_of_injective (originalFixedMiddleParameter_injective m)]
  simp only [Nat.card_prod,field_card,pow_two]

end SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleFixedParameters
