import SymmetricSubgroupAsymptotics.PermutationBinaryHead

/-!
# Actual trivial sections of a binary permutation module

A trivial quotient of an original subrepresentation is a quotient of
that subrepresentation's own coinvariants. This retains the original
ambient action and does not assume that the section embeds back into the
permutation module. The Boolean-width estimate is installed from the
proved permutation-head theorem, not supplied as an additional premise.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

section SectionSpace

variable {k G V : Type} [Field k] [Group G]
    [AddCommGroup V] [Module k V] {ρ : Representation k G V}

/-- The original lower subrepresentation as a literal subspace of its
original upper preimage, using the stated inclusion. -/
def subrepresentationSectionLower (L M : Subrepresentation ρ) (hLM : L ≤ M) :
    Submodule k M.toSubmodule :=
  LinearMap.range (Submodule.inclusion
    (show L.toSubmodule ≤ M.toSubmodule from hLM))

/-- The actual section M/L, with no claim that it is an ambient submodule. -/
abbrev SubrepresentationSection (L M : Subrepresentation ρ) (hLM : L ≤ M) :=
  M.toSubmodule ⧸ subrepresentationSectionLower L M hLM

end SectionSpace

section Permutation

variable {k G X W : Type} [Field k] [Group G] [Finite G]
    [Finite X] [MulAction G X] [MulAction.IsPretransitive G X]
    [AddCommGroup W] [Module k W]

/-- Any actual surjective invariant map from the original preimage
factors through its intrinsic coinvariants. The target need not embed in
the permutation module, and no faithfulness of the G-action is required. -/
theorem twoGroup_permutation_trivial_quotient_finrank_le
    (hG : IsPGroup 2 G) (t : ℕ) (hcard : Nat.card X = 2^t) (x : X)
    (M : Subrepresentation (permutationFunctionRepresentation k G X))
    (q : M.toSubmodule →ₗ[k] W) (hq : Function.Surjective q)
    (htrivial : ∀ (g : G) (m : M.toSubmodule),
      q (M.toRepresentation g m) = q m) :
    Module.finrank k W ≤ t.choose (t/2) := by
  classical
  letI := Fintype.ofFinite X
  have hinvariant : ∀ g : G, q.comp (M.toRepresentation g) = q := by
    intro g
    apply LinearMap.ext
    exact htrivial g
  let q' : M.toRepresentation.Coinvariants →ₗ[k] W :=
    Representation.Coinvariants.lift M.toRepresentation q hinvariant
  have hq' : Function.Surjective q' := by
    intro w
    obtain ⟨m,hm⟩ := hq w
    exact ⟨Representation.Coinvariants.mk M.toRepresentation m,hm⟩
  have hdim : Module.finrank k W ≤ Module.finrank k M.toRepresentation.Coinvariants :=
    LinearMap.finrank_le_finrank_of_surjective hq'
  rw [← representationHead_finrank_eq_coinvariants] at hdim
  exact hdim.trans (twoGroup_permutationSubrepresentationHead_le_width hG t hcard x M)

/-- For original invariant L≤M, the condition g·m−m∈L is precisely
triviality of the induced section action. It is tested for every original
group element and every vector of M; no section embedding is assumed. -/
theorem twoGroup_permutation_trivial_section_finrank_le
    (hG : IsPGroup 2 G) (t : ℕ) (hcard : Nat.card X = 2^t) (x : X)
    (L M : Subrepresentation (permutationFunctionRepresentation k G X)) (hLM : L ≤ M)
    (htrivial : ∀ (g : G) (m : M.toSubmodule),
      permutationFunctionRepresentation k G X g (m : X → k) - (m : X → k) ∈
        L.toSubmodule) :
    Module.finrank k (SubrepresentationSection L M hLM) ≤ t.choose (t/2) := by
  apply twoGroup_permutation_trivial_quotient_finrank_le hG t hcard x M
    (subrepresentationSectionLower L M hLM).mkQ
    (subrepresentationSectionLower L M hLM).mkQ_surjective
  intro g m
  apply (Submodule.Quotient.eq _).mpr
  change M.toRepresentation g m - m ∈
    LinearMap.range (Submodule.inclusion
      (show L.toSubmodule ≤ M.toSubmodule from hLM))
  refine ⟨⟨permutationFunctionRepresentation k G X g (m : X → k) - (m : X → k),
    htrivial g m⟩,?_⟩
  apply Subtype.ext
  rfl

end Permutation
end SymmetricSubgroupAsymptotics

end
