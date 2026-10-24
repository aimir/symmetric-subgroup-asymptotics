import SymmetricSubgroupAsymptotics.CFSGFFourOriginalHighCoefficientBlock

/-! The remaining selected high-root integer mixed certificates.
Each reduction checks one root and four-by-four node choices, evaluated
pointwise on the finite coefficient slots. No source or matrix-image
identity is inferred from the candidate producer. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGFFourOriginalUpperCoefficientCertificates
open CFSGFFourOriginalRootFamilyProfile CFSGFFourOriginalHighCoefficientBlock

theorem mixed_eighteen : mixedIdentity (.inl 18) := by
  intro i a
  funext k
  revert i a k
  decide +kernel

theorem mixed_nineteen : mixedIdentity (.inl 19) := by
  intro i a
  funext k
  revert i a k
  decide +kernel

theorem mixed_twenty : mixedIdentity (.inl 20) := by
  intro i a
  funext k
  revert i a k
  decide +kernel

theorem mixed_twenty_one : mixedIdentity (.inl 21) := by
  intro i a
  funext k
  revert i a k
  decide +kernel

theorem mixed_twenty_two : mixedIdentity (.inl 22) := by
  intro i a
  funext k
  revert i a k
  decide +kernel

theorem mixed_twenty_three : mixedIdentity (.inl 23) := by
  intro i a
  funext k
  revert i a k
  decide +kernel

private theorem high_indices : ∀j:Fin 24,7≤rootHeight j→
    j=18∨j=19∨j=20∨j=21∨j=22∨j=23 := by decide +kernel

theorem mixed_at_upper_height (j:Fin 24) (hj:7≤rootHeight j) : mixedIdentity (.inl j) := by
  rcases high_indices j hj with rfl|rfl|rfl|rfl|rfl|rfl
  · exact mixed_eighteen
  · exact mixed_nineteen
  · exact mixed_twenty
  · exact mixed_twenty_one
  · exact mixed_twenty_two
  · exact mixed_twenty_three

end SymmetricSubgroupAsymptotics.CFSGFFourOriginalUpperCoefficientCertificates
