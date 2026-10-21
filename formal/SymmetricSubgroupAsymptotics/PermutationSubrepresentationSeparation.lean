import SymmetricSubgroupAsymptotics.PermutationSubrepresentationHead

/-! A point-separating actual permutation submodule is faithful. This
criterion is independent of its dimension and retains the literal action. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

theorem permutationSubrepresentation_injective_of_separating
    {k I : Type} [Field k] {H : Subgroup (Equiv.Perm I)}
    (W : Subrepresentation (permutationFunctionRepresentation k H I))
    (hsep : ∀ x y : I,(∀ v : I → k,v∈W.toSubmodule → v x=v y) → x=y) :
    Function.Injective W.toRepresentation := by
  intro a b he
  apply inv_injective
  apply Subtype.ext
  apply Equiv.ext
  intro x
  apply hsep
  intro v hv
  exact congrArg (fun L : Module.End k W.toSubmodule => (L ⟨v,hv⟩).val x) he

end SymmetricSubgroupAsymptotics
